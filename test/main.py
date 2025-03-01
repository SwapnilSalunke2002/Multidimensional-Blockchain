import hashlib
import datetime
import time
import json
import random
import math
import heapq
import inspect
from collections import deque, defaultdict
from datetime import datetime


############################################
# Helper Function for Input Conversion
############################################

def prompt_for_parameter(param_name: str, param_type: type):
    """
    Prompts the user to enter a value for a given parameter and converts it to the desired type.
    Note: For list and dict, the conversion follows the original behavior.
    """
    raw_value = input(f"Enter {param_name}: ").strip()
    try:
        if param_type == int:
            return int(raw_value)
        elif param_type == float:
            return float(raw_value)
        elif param_type == list:
            # This will create a list of characters from the input.
            return list(raw_value)
        elif param_type == dict:
            # This converts the input string to a dict (may not work as expected if input is not in proper format)
            return dict(raw_value)
        else:
            return raw_value
    except Exception as e:
        print(f"Error converting input for {param_name}: {e}")
        return raw_value

def sim_prompt_for_parameter(param_name: str, param_type: type):
    """
    Prompts the user to enter a value for a given parameter and converts it to the desired type.
    Note: For list and dict, the conversion follows the original behavior.
    """
    try:
        if param_type == int:
            return 0
        elif param_type == float:
            return 0.0
        elif param_type == list:
            # This will create a list of characters from the input.
            return []
        elif param_type == dict:
            # This converts the input string to a dict (may not work as expected if input is not in proper format)
            return {}
        else:
            return 'Name'
    except Exception as e:
        print(f"Error converting input for {param_name}: {e}")
        return raw_value

############################################
# Smart Instance: Instantiator Class
############################################

class Instantiator:    
    def __init__(self, script: str, block_hash:str):
        self.smarthash = block_hash
        self.namespace = {"SIEvent":self.SIEvent}
        exec(script, self.namespace)
        self.classes = {name: obj for name, obj in self.namespace.items() if isinstance(obj, type)}

    def SIEvent(self,data):
        transaction = {
            'EventMetadata': {
                'timestamp': datetime.now().timestamp(),
                'smarthash': self.smarthash,
            },
            'body': data
        }
        return transaction
    
    def get_class_names(self):
        return list(self.classes.keys())
    
    def instantiate(self, class_name: str, *args, **kwargs):
        if class_name not in self.classes:
            raise ValueError(f"Class '{class_name}' not found in the provided script.")
        return self.classes[class_name](*args, **kwargs)
    
    def list_members(self, class_name: str):
        if class_name not in self.classes:
            raise ValueError(f"Class '{class_name}' not found in the provided script.")
        
        cls = self.classes[class_name]
        member_functions = [
            name for name, func in inspect.getmembers(cls, predicate=inspect.isfunction)
            if not name.startswith('__') and not name.startswith('_') and not name.startswith('SIEvent')
        ]
        
        try:
            sig = inspect.signature(cls.__init__)
            dummy_args = {}
            for param_name, param in sig.parameters.items():
                if param_name == 'self':
                    continue
                dummy_args[param_name] = param.default if param.default is not param.empty else f"dummy_{param_name}"
            instance = cls(**dummy_args)
            member_variables = list(vars(instance).keys())
        except Exception as e:
            member_variables = f"Could not instantiate class to list member variables: {e}"
        
        return member_variables, member_functions
    
    def run_member_function(self, instance, function_name: str, *args, **kwargs):
        if hasattr(instance, function_name):
            method = getattr(instance, function_name)
            return method(*args, **kwargs)
        else:
            raise AttributeError(f"Method '{function_name}' not found in instance of {type(instance).__name__}")
    
    def run_all_member_functions(self, instance, functions_params: dict = None):
        outputs = {}
        member_functions = [
            name for name, func in inspect.getmembers(instance, predicate=inspect.ismethod)
            if not name.startswith('__') and not name.startswith('_')
        ]
        for func_name in member_functions:
            args, kwargs = (), {}
            if functions_params and func_name in functions_params:
                args, kwargs = functions_params[func_name]
            try:
                outputs[func_name] = self.run_member_function(instance, func_name, *args, **kwargs)
            except Exception as e:
                outputs[func_name] = f"Error: {e}"
        return outputs
    
    def instantiate_composite(self, *args, **kwargs):
        if not self.classes:
            raise ValueError("No classes loaded from the provided script.")
        
        def get_depth(cls):
            depth = 0
            for base in cls.__mro__:
                if base is object:
                    break
                depth += 1
            return depth
        
        most_derived = max(self.classes.values(), key=get_depth)
        mro_set = set(most_derived.__mro__)
        other_bases = tuple(cls for cls in self.classes.values() 
                            if cls is not most_derived and cls not in mro_set)
        
        if not other_bases:
            Composite = most_derived
        else:
            bases = (most_derived,) + other_bases
            Composite = type("Composite", bases, {})
        
        return Composite(*args, **kwargs)
    
    def get_composite_init_signature(self):
        """
        Returns the signature of the __init__ method used by the composite instantiator.
        """
        if not self.classes:
            raise ValueError("No classes loaded from the provided script.")
        
        def get_depth(cls):
            depth = 0
            for base in cls.__mro__:
                if base is object:
                    break
                depth += 1
            return depth
        
        most_derived = max(self.classes.values(), key=get_depth)
        return inspect.signature(most_derived.__init__)
    
    def instantiate_composite_with_params(self, params: dict):
        """
        Instantiates the composite class using parameters from the provided dictionary.
        
        Raises:
            ValueError: If a required parameter is missing.
        """
        sig = self.get_composite_init_signature()
        required_params = [name for name, param in sig.parameters.items() if name != "self"]
        
        for param in required_params:
            if param not in params:
                raise ValueError(f"Missing required parameter: {param}")
        
        return self.instantiate_composite(**params)


############################################
# BlockData: Stores the Block's Data
############################################

class BlockData:
    def __init__(self, value=None):
        self.transactions = value if isinstance(value, dict) else {"body": value}

    def __str__(self):
        return f"BlockData({self.transactions})"

############################################
# Block Class
############################################

class Block:
    def __init__(self, dir_neighbors, position=None, data=None, instance_script=None):
        self.data = BlockData(data)
        self.neighbors = set(dir_neighbors)  # Set of neighbor block hashes
        self.position = position if position is not None else (0, 0, 0)
        self.hash = self.compute_hash()  # Hash is computed after initialization
        self.Smart_Instance = Instantiator(instance_script,self.hash) if instance_script is not None else None

    def compute_hash(self):
        """Compute hash based on position, data, and neighbor hashes."""
        sha = hashlib.sha256()
        position_str = str(self.position)
        data_str = json.dumps(self.data.transactions, sort_keys=True)
        neighbors_str = ''.join(sorted(self.neighbors))  # Sort for consistency
        sha.update(f"{position_str}{data_str}{neighbors_str}".encode('utf-8'))
        return sha.hexdigest()

############################################
# MultiDimensionalBlockchain Class
############################################

class MultiDimensionalBlockchain:
    def __init__(self):
        self.blocks = {}  # Maps block hash to Block objects
        self.positions_map = {}  # Maps (x, y, z) to block hash
        self.open_positions = set()  # Positions adjacent to an existing block
        self.proposer = "mdb_auth"
        self.reverse_graph = defaultdict(set)

        # Create genesis block at (0,0,0)
        genesis_position = (0, 0, 0)
        genesis = Block([], genesis_position, 'Genesis Block')
        genesis_hash = genesis.hash
        self.blocks[genesis_hash] = genesis
        self.positions_map[genesis_position] = genesis_hash

        for dx, dy, dz in [(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)]:
            pos = (genesis_position[0] + dx, genesis_position[1] + dy, genesis_position[2] + dz)
            self.open_positions.add(pos)

    def add_block(self, data, position=None,instance_script=None):
        if position is None:
            if self.open_positions:
                position = min(self.open_positions, key=lambda pos: pos[0]**2 + pos[1]**2 + pos[2]**2)
                self.open_positions.remove(position)
            else:
                print("No available open positions to place new block.")
                return None
        else:
            if position in self.positions_map:
                print("Provided position is already occupied.")
                return None
            adjacent_found = any(
                (position[0] + dx, position[1] + dy, position[2] + dz) in self.positions_map
                for dx, dy, dz in [(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)]
            )
            if not adjacent_found:
                print("Provided position is not adjacent to any existing block.")
                return None
            if position in self.open_positions:
                self.open_positions.remove(position)

        # Collect neighbor hashes
        neighbors = []
        for dx, dy, dz in [(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)]:
            neighbor_pos = (position[0] + dx, position[1] + dy, position[2] + dz)
            if neighbor_pos in self.positions_map:
                neighbor_hash = self.positions_map[neighbor_pos]
                neighbors.append(neighbor_hash)
            else:
                self.open_positions.add(neighbor_pos)

        # Create and store new block
        new_block = Block(neighbors, position, data,instance_script)
        new_block_hash = new_block.hash
        self.blocks[new_block_hash] = new_block
        self.positions_map[position] = new_block_hash

        # Update reverse graph
        for neighbor_hash in neighbors:
            self.reverse_graph[neighbor_hash].add(new_block_hash)

        return new_block

    def get_adjacency_list(self):
        """Return adjacency list with abbreviated hashes for readability."""
        return {
            block_hash[:8]: [neighbor_hash[:8] for neighbor_hash in block.neighbors]
            for block_hash, block in self.blocks.items()
        }

    def validate_blockchain(self):
        for block_hash, block in self.blocks.items():
            if block_hash != block.compute_hash():
                return False
            for neighbor_hash in block.neighbors:
                if neighbor_hash not in self.blocks:
                    return False
        return True

    def get_neighbors(self, block_hash):
        """Get all neighbors of a block, including outgoing and incoming edges."""
        block = self.blocks[block_hash]
        neighbors = set(block.neighbors)
        incoming = self.reverse_graph[block_hash]
        return neighbors.union(incoming)

    def shortest_path_dijkstra(self, start_hash, end_hash):
        distances = {block_hash: float('inf') for block_hash in self.blocks}
        previous = {block_hash: None for block_hash in self.blocks}
        distances[start_hash] = 0
        visited = set()
        queue = [(0, start_hash)]
        while queue:
            current_distance, current = heapq.heappop(queue)
            if current == end_hash:
                break
            if current in visited:
                continue
            visited.add(current)
            for neighbor in self.get_neighbors(current):  # Use get_neighbors for bidirectional
                distance = current_distance + 1
                if distance < distances[neighbor]:
                    distances[neighbor] = distance
                    previous[neighbor] = current
                    heapq.heappush(queue, (distance, neighbor))
        path = []
        current = end_hash
        while current is not None:
            path.insert(0, current)
            current = previous[current]
        if path and path[0] != start_hash:
            return None
        return path

    def shortest_path_a_star(self, start_hash, end_hash):
        def heuristic(a_hash, b_hash):
            a = self.blocks[a_hash]
            b = self.blocks[b_hash]
            return math.sqrt((a.position[0] - b.position[0]) ** 2 + (a.position[1] - b.position[1]) ** 2 + 
                             (a.position[2] - b.position[2]) ** 2)
        open_set = {start_hash}
        came_from = {}
        g_score = {block_hash: float('inf') for block_hash in self.blocks}
        f_score = {block_hash: float('inf') for block_hash in self.blocks}
        g_score[start_hash] = 0
        f_score[start_hash] = heuristic(start_hash, end_hash)
        open_heap = [(f_score[start_hash], start_hash)]
        while open_heap:
            current_f, current = heapq.heappop(open_heap)
            if current == end_hash:
                path = []
                while current in came_from:
                    path.insert(0, current)
                    current = came_from[current]
                path.insert(0, start_hash)
                return path
            open_set.discard(current)
            for neighbor in self.get_neighbors(current):
                tentative_g_score = g_score[current] + 1
                if tentative_g_score < g_score[neighbor]:
                    came_from[neighbor] = current
                    g_score[neighbor] = tentative_g_score
                    f_score[neighbor] = tentative_g_score + heuristic(neighbor, end_hash)
                    if neighbor not in open_set:
                        open_set.add(neighbor)
                        heapq.heappush(open_heap, (f_score[neighbor], neighbor))
        return None

    def find_path(self, start_hash, target_hash):
        """Find the shortest path between start_hash and target_hash using BFS."""
        if start_hash not in self.blocks or target_hash not in self.blocks:
            return None
        visited = set()
        queue = deque([start_hash])
        parent = {start_hash: None}
        while queue:
            current_hash = queue.popleft()
            if current_hash == target_hash:
                path = []
                while current_hash is not None:
                    path.append(current_hash)
                    current_hash = parent[current_hash]
                return path[::-1]
            if current_hash not in visited:
                visited.add(current_hash)
                for neighbor_hash in self.get_neighbors(current_hash):
                    if neighbor_hash not in visited:
                        queue.append(neighbor_hash)
                        if neighbor_hash not in parent:
                            parent[neighbor_hash] = current_hash
        return None

    def print_path(self, start_hash, target_hash):
        """Print the path between two blocks with their positions."""
        path = self.find_path(start_hash, target_hash)
        if path is None:
            print(f"No path exists between Block {start_hash[:8]}... and Block {target_hash[:8]}...")
            return []
        else:
            print(f"Path from Block {start_hash[:8]}... to Block {target_hash[:8]}...:")
            for block_hash in path:
                block = self.blocks[block_hash]
                print(f"Block Hash: {block_hash[:8]}..., Position: {block.position}, Neighbours: {[h[:8] for h in block.neighbors]}")
            return path

    def get_position(self, block_hash):
        return self.blocks[block_hash].position

    def euclidean_distance(self, pos1, pos2):
        return sqrt(sum((a - b) ** 2 for a, b in zip(pos1, pos2)))

    def find_path2(self, start_hash, target_hash):
        """Find the shortest path using A* algorithm."""
        if start_hash not in self.blocks or target_hash not in self.blocks:
            return None
        start_pos = self.get_position(start_hash)
        target_pos = self.get_position(target_hash)

        def heuristic(block_hash):
            return self.euclidean_distance(self.get_position(block_hash), target_pos)

        frontier = []
        heapq.heappush(frontier, (0 + heuristic(start_hash), 0, start_hash))
        came_from = {start_hash: None}
        cost_so_far = {start_hash: 0}

        while frontier:
            _, current_cost, current_hash = heapq.heappop(frontier)
            if current_hash == target_hash:
                path = []
                while current_hash is not None:
                    path.append(current_hash)
                    current_hash = came_from[current_hash]
                return path[::-1]
            for neighbor_hash in self.get_neighbors(current_hash):
                new_cost = current_cost + 1
                if neighbor_hash not in cost_so_far or new_cost < cost_so_far[neighbor_hash]:
                    cost_so_far[neighbor_hash] = new_cost
                    priority = new_cost + heuristic(neighbor_hash)
                    heapq.heappush(frontier, (priority, new_cost, neighbor_hash))
                    came_from[neighbor_hash] = current_hash
        return None

    def execute_smart_instance(self, block_hash):
        if block_hash not in self.blocks:
            print("Invalid block hash.")
            return 0

        if self.blocks[block_hash].Smart_Instance == None:
            print("Could not locate Smart Instance block or block does not contain smart instance")
            return 0
        """
        Initializes a smart instance for a block by prompting for required parameters.
        """

        # Function to set values dynamically while ignoring extra keys
        def set_values_dynamically(obj, values: dict):
            valid_keys = obj.__dict__.keys()  # Get only allowed attributes
            for key, value in values.items():
                if key in valid_keys:  # Update only valid attributes
                    setattr(obj, key, value)


        composite_sig = self.blocks[block_hash].Smart_Instance.get_composite_init_signature()
        params = {}
        for pname, param in composite_sig.parameters.items():
            if pname != "self":
                try:
                    req_trans = None
                    params[pname] = prompt_for_parameter(pname, param.annotation)

                    for hkey, block in reversed(self.blocks.items()):
                        transaction = block.data.transactions

                        if "EventMetadata" in transaction and transaction["EventMetadata"]["smarthash"]==block_hash:
                            if pname in transaction['body']:
                                if transaction['body'][pname] == params[pname]:
                                    req_trans = transaction['body']
                                    break

             
                except Exception as e:
                    print(e)


        composite_instance = self.blocks[block_hash].Smart_Instance.instantiate_composite_with_params(params)
        if req_trans is not None:
            set_values_dynamically(composite_instance,req_trans)
        else:
            print("Could not retrieve transaction...")

        """
        Allows the user to select and run a smart instance method on a given block.
        """
            
        instance = composite_instance
        funcs = [(name, m) for name, m in inspect.getmembers(instance, predicate=inspect.ismethod)
                if not name.startswith('__') and not name.startswith('_')]
        if not funcs:
            print("No smart instance functions available.")
            return 0
        print("\nSmart Instance Functions:")
        for i, (fname, _) in enumerate(funcs):
            print(f"{i+1}. {fname}")
        choice = input("Run which function? (Enter number, blank to skip): ").strip()
        if not choice:
            return 0
        try:
            idx = int(choice) - 1
            if idx < 0 or idx >= len(funcs):
                print("Invalid choice.")
                return 0
            chosen_func = funcs[idx][1]
        except Exception as e:
            print("Invalid input:", e)
            return 0
        sig = inspect.signature(chosen_func)
        params = {}
        for pname, param in sig.parameters.items():
            if pname != "self":
                params[pname] = prompt_for_parameter(pname, param.annotation)
        try:
            transaction = chosen_func(**params) if params else chosen_func()
        
            if transaction != None and type(transaction) is dict and 'EventMetadata' in transaction:
                # transaction = create_block_transaction(result)
                print("Smart instance function result:", transaction)
                self.add_block(transaction)
            return transaction
        except Exception as e:
            print("Error running smart instance function:", e)
            return 0

            
def main():
    DEFAULT_INSTANCE_SCRIPT = """
class MovieTheater:
    def __init__(self, movie_name: str):
        self.movie_name = movie_name
        self.total_seats = 10
        self.booked_seats = set()  # Using a set to store booked seat numbers

    def book_ticket(self, seat_number: int) -> bool:
        if seat_number < 1 or seat_number > self.total_seats:
            print(f"Invalid seat number! Choose between 1 and {self.total_seats}.")
            return False
        if seat_number in self.booked_seats:
            print(f"Seat {seat_number} is already booked!")
            return False
        self.booked_seats.add(seat_number)
        print(f"Successfully booked seat {seat_number} for '{self.movie_name}'.")
        return {"Operation":"BookTicket","movie_name":self.movie_name,"booked_seats":self.booked_seats}

    def cancel_ticket(self, seat_number: int) -> bool:
        if seat_number in self.booked_seats:
            self.booked_seats.remove(seat_number)
            print(f"Seat {seat_number} booking has been canceled.")
            return True
        print(f"Seat {seat_number} is not booked.")
        return {"Operation":"CancelTicket","movie_name":self.movie_name,"booked_seats":self.booked_seats}

    def available_seats(self) -> list:
        return sorted(set(range(1, self.total_seats + 1)) - self.booked_seats)

"""
    blockchain = MultiDimensionalBlockchain()

    num_blocks = 100  # Reduced for testing; hashes are long strings
    for i in range(num_blocks):
        sim_block = blockchain.add_block(f'Simulating Block Addition at {i+1}')
        # print(f"Added block with hash: {sim_block.hash[:8]}...")

    menu = """
Please choose an option:
1. Add a new block
2. Print blockchain data
3. Display adjacency list (first N blocks)
4. Validate blockchain
5. Find Shortest Path between Two Blocks
6. Execute Smart Instance
7. Exit
"""
    while True:
        print(menu)
        choice = input("Enter your choice (1-7): ").strip()
        if choice == "1":
            data = input("Enter Smart Instance Name: ")

            use_script = 'y'
            if use_script:
                with open("/home/swapnil_salunke22/My Projects/MDBlockchain/src/main_script.txt", "r", encoding="utf-8") as file:
                    instance_script = file.read()  # Reads the whole file as a string
                    
                new_block = blockchain.add_block(data,instance_script=instance_script)
                print(f"New Smart Instance Block Added:\nHash: {new_block.hash} at position: {new_block.position}\n***Keep Smart Instance Block Key (Hash) Secure.***\n")
            else:
                new_block = blockchain.add_block(data)

            if new_block:
                print(f"Block added with hash: {new_block.hash}")
            else:
                print("Block addition failed.")

        elif choice == "2":
            print("Blockchain Data:")
            for block_hash, block in sorted(blockchain.blocks.items(), key=lambda x: x[0]):
                neighbor_hashes = [h[:8] for h in block.neighbors]
                print(f"Hash: {block_hash}, Data: {vars(block.data)}, Position: {block.position}, Neighbors: {neighbor_hashes}")
            print("")
            
        elif choice == "3":
            try:
                n = int(input("Enter number of blocks to display (default 10): ").strip() or 10)
            except:
                n = 10
            adj = blockchain.get_adjacency_list()
            print("Adjacency List (first N blocks):")
            for block_hash, neighbors in list(adj.items())[:n]:
                print(f"Block {block_hash}: Neighbors -> {neighbors}")
            print("")

        elif choice == "4":
            valid = blockchain.validate_blockchain()
            print(f"Blockchain validation result: {valid}\n")

        elif choice == "5":
            try:
                start_hash = input("Enter Starting block hash: ").strip()
                end_hash = input("Enter Ending block hash: ").strip()

                tic = time.time()
                path = blockchain.print_path(start_hash, end_hash)
                print(f"Path hashes: {[h[:8] for h in path]}, Hops: {len(path)}")
                print("Time delay for traversal:", time.time() - tic)
            except Exception as e:
                print("Invalid block hash:", e)

        elif choice == "6":
            try:
                key = input("Enter Block Hash Key to Execute Smart Instance: ").strip()

                blockchain.execute_smart_instance(key)

            except Exception as e:
                print("Smart Instance Execution Failed:",e)

        elif choice == "7":
            print("Exiting. Goodbye!")
            break
        else:
            print("Invalid choice. Try again.\n")

if __name__ == '__main__':
    main()