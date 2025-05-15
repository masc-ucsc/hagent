# hagent/tool/memory/test_few_shot_memory.py

import sys
import argparse
from pathlib import Path
from hagent.tool.memory.few_shot_memory_layer import FewShotMemory, Memory
from hagent.tool.memory.utils import normalize_code
from hagent.tool.compile import Diagnostic

def main():
    """
    Main function to demonstrate the few-shot memory system.
    Analyzes a program file, searches for similar bugs, and adds it to memory.
    """
    # Parse command line arguments - simplified to only require program path
    parser = argparse.ArgumentParser(description='HAgent Memory - Add and find programming bugs')
    parser.add_argument('-p', '--program', type=str, required=True, help='Path to a program file to analyze')
    parser.add_argument('-d', '--database', type=str, default="data/test_memory_database.yaml", 
                        help='Path to the memory database file')
    parser.add_argument('-o', '--output', type=str, default=None, 
                        help='Path to save the results (default: auto-generated)')
    args = parser.parse_args()
    
    # Process the specified program file
    test_program_path = Path(args.program)
    if not test_program_path.exists():
        print(f"Error: Program file not found at {test_program_path}")
        sys.exit(1)
    
    # Initialize memory system
    print(f"Initializing memory system...")
    memory_system = FewShotMemory(
        db_path=args.database
    )
    
    print(f"Memory system initialized with {len(memory_system.memories)} examples")
        
    # Read code from file
    test_code = Memory.read_code_file(test_program_path)
    if test_code is None:
        sys.exit(1)
    
    # Detect language
    language = Memory.detect_language(test_program_path)
    print(f"Detected language: {language}")
    
    # Get compiler errors and diagnostic
    compiler_errors, analysis, diagnostic = Memory.get_compiler_errors(test_code, language, test_program_path.name)
    
    # Update diagnostic with file path if it's not set
    if not diagnostic.file:
        diagnostic.file = str(test_program_path)
    
    # Find similar examples
    print("Searching for similar code...")
    matches = memory_system.find(
        err=diagnostic,
        fix_question=test_code
    )
    
    # Save results manually since we removed that from find()
    results_dir = Path("results")
    results_dir.mkdir(exist_ok=True)
    output_file = args.output or Memory.determine_output_file(None, test_program_path)
    Memory.process_matches(matches, test_code, output_file)
    
    # Check if an exact match exists
    memory_exists = False
    if matches:
        # The find method already returns exact matches first if they exist
        normalized_test_code = normalize_code(test_code)
        if normalize_code(matches[0].faulty_code) == normalized_test_code:
            memory_exists = True
            print(f"Memory already exists with ID: {matches[0].id}")
            print(f"Match confidence: {matches[0].confidence:.4f}")
            
            if matches[0].fix_answer:
                print(f"\nSuggested fix:")
                print(f"```")
                print(matches[0].fix_answer)
                print(f"```")
    
    # Add to memory only if it doesn't already exist
    if not memory_exists:
        memory_id = memory_system.add(
            err=diagnostic,
            fix_question=test_code,
            fix_answer=None
        )
        print(f"Added to memory with ID: {memory_id}")
    
    print(f"Memory saved to database at {memory_system.db_path}")
    print(f"Memory system contains {len(memory_system.memories)} examples")
    print(f"Results saved to {output_file}")

if __name__ == "__main__":
    main()