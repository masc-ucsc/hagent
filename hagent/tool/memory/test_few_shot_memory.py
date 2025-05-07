import sys
import argparse
from pathlib import Path
from few_shot_memory_layer import FewShotMemory, Memory
from utils import normalize_code

def main():
    # Parse command line arguments - simplified to only require program path
    parser = argparse.ArgumentParser(description='Add C++ program to few-shot memory database')
    parser.add_argument('-p', '--program', type=str, required=True, help='Path to a C++ program file to add to memory')
    args = parser.parse_args()
    
    # Initialize paths with default database
    database_path = "data/sample_memories.yaml"
    data_dir, sample_db_path, test_db_path = Memory.initialize_paths(database_path)
    
    # Set up cache directory for memories
    cache_dir = Path("cached_memories")
    cache_dir.mkdir(exist_ok=True)
    memory_cache_file = cache_dir / "memory_cache_bugs.pkl"
    
    # Initialize memory system
    memory_system = FewShotMemory(db_path=str(test_db_path))
    
    # Load cached memories or create new ones
    Memory.load_or_create_memories(memory_system, memory_cache_file, sample_db_path)
    
    # Process the specified program file
    test_program_path = Path(args.program)
    if not test_program_path.exists():
        print(f"Error: Program file not found at {test_program_path}")
        sys.exit(1)
        
    test_code = Memory.read_cpp_file(test_program_path)
    if test_code is None:
        sys.exit(1)
    
    # Find similar examples first
    matches = memory_system.find(original_code=test_code)
    
    # Check if an exact match exists
    memory_exists = False
    if matches:
        # The find method already returns exact matches first if they exist
        normalized_test_code = normalize_code(test_code)
        if normalize_code(matches[0].faulty_code) == normalized_test_code:
            memory_exists = True
            print(f"Memory already exists with ID: {matches[0].id}")
    
    # Add to memory only if it doesn't already exist
    if not memory_exists:
        memory_id = memory_system.add(
            original_code=test_code,
            fixed_code=None,
            errors=None
        )
        print(f"Added to memory with ID: {memory_id}")
    
    # Determine output file
    output_file = f"results/{test_program_path.stem}_matches.yaml"
    
    # Process matches
    Memory.process_matches(matches, test_code, output_file)
    
    # Save databases
    Memory.save_databases(memory_system, test_db_path, data_dir)
    print(f"Memory saved to database at {test_db_path} and JSON equivalent")

if __name__ == "__main__":
    main()