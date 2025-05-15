# hagent/tool/memory/test_few_shot_memory.py

import sys
import argparse
from pathlib import Path
from hagent.tool.memory.few_shot_memory_layer import FewShotMemory, Memory
from hagent.tool.memory.utils import normalize_code

def main():
    # Parse command line arguments - simplified to only require program path
    parser = argparse.ArgumentParser(description='Add C++ program to few-shot memory database')
    parser.add_argument('-p', '--program', type=str, required=True, help='Path to a C++ program file to add to memory')
    args = parser.parse_args()
    
    # Process the specified program file
    test_program_path = Path(args.program)
    if not test_program_path.exists():
        print(f"Error: Program file not found at {test_program_path}")
        sys.exit(1)
    
    # Initialize memory system - paths are now handled automatically
    print(f"Initializing memory system...")
    memory_system = FewShotMemory(
        db_path="data/test_memory_database.yaml"
    )
    
    print(f"Memory system initialized with {len(memory_system.memories)} memories")
        
    # Read code from file
    test_code = Memory.read_code_file(test_program_path)
    if test_code is None:
        sys.exit(1)
    
    # Detect language
    language = Memory.detect_language(test_program_path)
    print(f"Detected language: {language}")
    
    # Find similar examples first - now with automatic results saving
    print("Searching for similar code...")
    matches = memory_system.find(
        original_code=test_code,
        program_path=test_program_path,
        save_results=True
    )
    
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
        # Get compiler errors for better analysis
        compiler_errors, _ = Memory.get_compiler_errors(test_code, language, test_program_path.name)
        
        memory_id = memory_system.add(
            original_code=test_code,
            fixed_code=None,
            errors=compiler_errors
        )
        print(f"Added to memory with ID: {memory_id}")
    
    print(f"Memory saved to database at {memory_system.db_path}")
    print(f"Memory system contains {len(memory_system.memories)} examples")

if __name__ == "__main__":
    main()