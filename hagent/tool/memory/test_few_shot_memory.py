import os
import sys
import argparse
import pickle
from pathlib import Path
from datetime import datetime
from few_shot_memory_layer import FewShotMemory
from utils import load_cpp_bugs_dataset, CppBugExample, normalize_code
from ruamel.yaml import YAML

def memory_to_dict(item):
    """Convert a memory item to a dictionary for serialization"""
    return {
        "id": item.id,
        "content": item.content,
        "error_type": getattr(item, 'error_type', 'unknown'),
        "bug_category": getattr(item, 'bug_category', 'unknown'),
        "faulty_code": item.faulty_code,
        "fixed_code": getattr(item, 'fixed_code', ""),
        "timestamp": item.timestamp,
        "keywords": getattr(item, 'keywords', []),
        "tags": getattr(item, 'tags', []),
        "context": getattr(item, 'context', ""),
        "compiler_errors": getattr(item, 'compiler_errors', []),
    }

def read_cpp_file(file_path):
    """Read C++ code from a file"""
    try:
        with open(file_path, 'r') as f:
            return f.read()
    except Exception as e:
        print(f"Error reading file {file_path}: {e}")
        return None

def save_examples_to_yaml(matches, query_code, output_file, exact_match=False):
    """Save found examples to a YAML file"""
    # Create the output directory if it doesn't exist
    output_path = Path(output_file)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    
    # Prepare the data to save
    result = {
        "query": {
            "code": query_code,
            "timestamp": datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        },
        "results": {
            "count": len(matches),
            "exact_match_found": exact_match,
            "matches": [memory_to_dict(match) for match in matches]
        }
    }
    
    # Save to YAML file
    yaml = YAML()
    yaml.indent(mapping=2, sequence=4, offset=2)
    with open(output_file, 'w') as f:
        yaml.dump(result, f)
    
    print(f"\nResults saved to {output_file}")

def main():
    # Parse command line arguments
    parser = argparse.ArgumentParser(description='Test few-shot memory system with C++ bug examples')
    parser.add_argument('-p', '--program', type=str, required=True, help='Path to a C++ program file to test')
    parser.add_argument('-d', '--database', type=str, default="data/sample_memories.yaml",
                        help='Path to the memory database file (default: data/sample_memories.yaml)')
    parser.add_argument('-o', '--output', type=str, help='Path to save the results')
    parser.add_argument('-b', '--backend', type=str, default="openai",
                        help='Backend to use (openai or ollama)')
    parser.add_argument('-m', '--model', type=str, default="gpt-4o-mini",
                        help='Model to use (default: gpt-4o-mini)')
    args = parser.parse_args()
    
    # Initialize paths
    data_dir = Path("data")
    sample_db_path = Path(args.database)
    
    if not sample_db_path.exists():
        print(f"Error: Database file not found at {sample_db_path}")
        sys.exit(1)
    
    # Create a test output database so we don't modify the original
    test_db_path = data_dir / "test_memory_database.yaml"
    if test_db_path.exists():
        os.remove(test_db_path)  # Start fresh for the demo
    
    # Set up cache directory for memories
    cache_dir = Path(f"cached_memories_cpp_{args.backend}_{args.model}")
    cache_dir.mkdir(exist_ok=True)
    memory_cache_file = cache_dir / "memory_cache_cpp_bugs.pkl"
    
    # Initialize memory system
    print(f"\n--- Initializing memory system ---")
    empty_memory = FewShotMemory(db_path=str(test_db_path))
    
    # Load cached memories or create new ones
    if memory_cache_file.exists():
        print(f"Loading cached memories from {memory_cache_file}")
        try:
            with open(memory_cache_file, 'rb') as f:
                empty_memory.memories = pickle.load(f)
            print(f"Successfully loaded {len(empty_memory.memories)} memories")
        except Exception as e:
            print(f"Error loading cached memories: {e}. Will recreate memories.")
            create_new_memories = True
        else:
            create_new_memories = False
    else:
        print(f"No cached memories found. Creating new memories.")
        create_new_memories = True
    
    # Create new memories if needed
    if create_new_memories:
        # Load examples from the original database
        cpp_bug_examples = load_cpp_bugs_dataset(sample_db_path)
        print(f"Loaded {len(cpp_bug_examples)} examples from {sample_db_path}")
        
        # Add examples to our memory system
        print(f"Adding examples to memory system...")
        for example in cpp_bug_examples:
            empty_memory.add_from_example(example)
            
        # Cache memories for future runs
        with open(memory_cache_file, 'wb') as f:
            pickle.dump(empty_memory.memories, f)
        print(f"Successfully cached {len(empty_memory.memories)} memories")
    
    # Test with the specified program file
    test_program_path = Path(args.program)
    if not test_program_path.exists():
        print(f"Error: Program file not found at {test_program_path}")
        sys.exit(1)
        
    print(f"\n--- Testing with provided C++ file: {test_program_path} ---")
    test_code = read_cpp_file(test_program_path)
    if test_code is None:
        sys.exit(1)
        
    print(f"Code to analyze:")
    print("```")
    print(test_code)
    print("```")
    
    # Find similar examples
    matches = empty_memory.find(test_code)
    
    # Determine output file
    output_file = args.output
    if not output_file:
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        file_name = test_program_path.stem
        output_file = f"results/{file_name}_matches_{timestamp}.yaml"
    
    # Process matches
    exact_match = False
    
    if matches:
        print(f"Found {len(matches)} similar examples")
        
        # Brief summary of top match
        top_match = matches[0]
        print(f"\nTop match: {top_match.content}")
        print(f"Error type: {getattr(top_match, 'error_type', 'unknown')}")
        
        # Check for exact match
        if normalize_code(top_match.faulty_code) == normalize_code(test_code):
            exact_match = True
            print("\nExact match found! Suggested fix will be in the output file.")
            
            # Print suggested fix
            if top_match.fixed_code:
                print("\nSuggested fix:")
                print("```")
                print(top_match.fixed_code)
                print("```")
                
        # Save to YAML
        save_examples_to_yaml(matches, test_code, output_file, exact_match)
    else:
        print("No similar examples found")
        save_examples_to_yaml([], test_code, output_file, False)
    
    # Save databases
    print(f"\n--- Database statistics ---")
    print(f"Examples in memory: {len(empty_memory.memories)}")
    
    # Save to YAML
    empty_memory.save_database(str(test_db_path))
    print(f"Saved to: {test_db_path}")
    
    # Save a copy in JSON format
    json_db_path = data_dir / "test_memory_database.json"
    if json_db_path.exists():
        os.remove(json_db_path)
    empty_memory.save_database(str(json_db_path))
    print(f"Also saved database in JSON format to: {json_db_path}")
    
    print("\nTest completed successfully!")

if __name__ == "__main__":
    main()