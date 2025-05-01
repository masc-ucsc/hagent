#!/usr/bin/env python3
import os
import sys
import json
import argparse
import difflib
from pathlib import Path
from typing import List, Dict, Any, Optional, Tuple, Union

# Import our memory components
from hagent.tool.memory.few_shot_memory import FewShotMemory, Memory
from hagent.tool.memory.db_memory_store import SQLiteMemoryStore

def compile_code(code: str, language: str) -> List[str]:
    """Compile code and return error messages."""
    import tempfile
    import subprocess
    
    errors = []
    
    # Only handle C++ for this example
    if language == "cpp":
        with tempfile.NamedTemporaryFile(suffix='.cpp', delete=False) as tmp:
            tmp_path = tmp.name
            tmp.write(code.encode('utf-8'))
        
        try:
            # Try Clang++
            try:
                result = subprocess.run(['clang++', '-fsyntax-only', '-Wall', '-std=c++17', tmp_path], 
                                      capture_output=True, text=True, timeout=10)
                
                if result.returncode != 0:
                    errors = [line for line in result.stderr.strip().split('\n') if line]
            except (FileNotFoundError, subprocess.TimeoutExpired):
                # Try GCC instead
                try:
                    result = subprocess.run(['g++', '-fsyntax-only', '-Wall', '-std=c++17', tmp_path], 
                                          capture_output=True, text=True, timeout=10)
                    
                    if result.returncode != 0:
                        errors = [line for line in result.stderr.strip().split('\n') if line]
                except (FileNotFoundError, subprocess.TimeoutExpired):
                    errors.append("Could not compile - compiler not available")
        finally:
            if os.path.exists(tmp_path):
                os.remove(tmp_path)
    
    elif language == "python":
        with tempfile.NamedTemporaryFile(suffix='.py', delete=False) as tmp:
            tmp_path = tmp.name
            tmp.write(code.encode('utf-8'))
        
        try:
            # Check syntax errors
            result = subprocess.run([sys.executable, '-m', 'py_compile', tmp_path], 
                                  capture_output=True, text=True, timeout=10)
            
            if result.returncode != 0:
                errors = [line for line in result.stderr.strip().split('\n') if line]
        finally:
            if os.path.exists(tmp_path):
                os.remove(tmp_path)
    
    return errors

def extract_bug_type(errors: List[str], language: str) -> str:
    """Extract bug type from error messages."""
    if language == "cpp":
        error_text = " ".join(errors)
        
        if "expected ';'" in error_text:
            return "missing_semicolon"
        elif "undeclared identifier" in error_text:
            return "undeclared_variable"
        elif "expected ')'" in error_text or "expected '}'" in error_text:
            return "mismatched_brackets"
        elif "null pointer" in error_text:
            return "null_pointer"
    
    return "unknown"

def run_memory_retrieval(code: str, language: str = "cpp", memory_dir: str = None, 
                        verbose: bool = False, generate_data: bool = False):
    """Run memory retrieval with a code sample."""
    # Determine memory directory
    if memory_dir is None:
        memory_dir = os.path.join(os.path.dirname(__file__), "data")
    
    print(f"Using memory directory: {memory_dir}")
    os.makedirs(memory_dir, exist_ok=True)
    
    # Create database path
    db_path = os.path.join(memory_dir, "memory.db")
    
    # Check if database and embeddings exist
    if (not os.path.exists(db_path) or 
        not os.path.exists(os.path.join(memory_dir, "code_embeddings.npy"))) and not generate_data:
        print("⚠️ Database or embeddings not found. Generating test data first.")
        generate_data = True
    
    # Compile to get errors
    print(f"Compiling {language} code...")
    errors = compile_code(code, language)
    
    if errors:
        print(f"Found {len(errors)} compilation errors:")
        for i, error in enumerate(errors[:3]):
            print(f"{i+1}. {error}")
    else:
        print("No compilation errors found.")
    
    # Extract bug type
    bug_type = extract_bug_type(errors, language)
    print(f"Detected bug type: {bug_type}")
    
    # Generate test data if requested or needed
    if generate_data:
        from hagent.tool.memory.create_test_data import create_sample_data
        print("Generating test data...")
        os.makedirs(memory_dir, exist_ok=True)
        json_path, yaml_path = create_sample_data(
            os.path.join(memory_dir, "sample_memories.json"),
            os.path.join(memory_dir, "sample_memories.yaml"),
            create_embeddings=True
        )
        print(f"Generated test data: {json_path}")
        
        # Import data to SQLite
        from hagent.tool.memory.import_data import import_json_to_sqlite
        print("Importing data to SQLite...")
        import_json_to_sqlite(json_path, db_path, verbose=True, silent=False, create_embeddings=True)
    
    # Initialize memory system
    print("Initializing memory system...")
    try:
        memory = FewShotMemory(memory_dir=memory_dir, use_sqlite=True, db_path=db_path)
        
        # Verify that the memory system has loaded memories
        if not memory.memories and os.path.exists(db_path):
            print("Loading memories from database...")
            memory._load_memories()
            
        # Check if we have memories to work with
        if not memory.memories:
            print("⚠️ No memories available after initialization!")
            if not generate_data:
                print("Try running with -g flag to generate test data.")
    except Exception as e:
        print(f"Error initializing memory system: {e}")
        return []
    
    # Check if embeddings exist
    embeddings_file = os.path.join(memory_dir, "code_embeddings.npy")
    if not os.path.exists(embeddings_file):
        print("⚠️ Embeddings file not found: You need to generate embeddings")
        print("Run: python import_data.py -v --force-embeddings")
    
    # Create query based on error
    query = f"Fix {bug_type} in {language} code"
    
    # Retrieve similar examples using hybrid search
    print(f"Retrieving examples for query: '{query}'")
    results = memory.retrieve_memories(
        query=query,
        code=code,
        errors=errors,
        language=language,
        bug_type=bug_type,
        k=3
    )
    
    # Print results
    print(f"\nFound {len(results)} similar code examples:")
    
    if results:
        for i, memory in enumerate(results):
            print(f"\nMatch #{i+1}: {memory.content}")
            print(f"Bug type: {getattr(memory, 'error_type', 'unknown')}")
            print(f"Language: {memory.language}")
            
            # Print suggested fix if available
            if memory.fixed_code:
                print("\nSuggested fix:")
                # Generate diff
                diff = list(difflib.unified_diff(
                    code.splitlines(),
                    memory.fixed_code.splitlines(),
                    fromfile='faulty',
                    tofile='fixed',
                    lineterm=''
                ))
                if diff:
                    for line in diff[:20]:  # Limit to first 20 lines
                        print(line)
                else:
                    print("No differences found in fix")
            else:
                print("No fix available for this match.")
    else:
        print("No similar code examples found.")
    
    # Save detailed results to JSON if verbose
    if verbose:
        results_file = os.path.join(memory_dir, "retrieval_results.json")
        results_data = []
        
        for memory in results:
            results_data.append({
                "id": memory.id,
                "content": memory.content,
                "bug_type": getattr(memory, "error_type", "unknown"),
                "language": memory.language,
                "faulty_code": memory.faulty_code,
                "fixed_code": memory.fixed_code
            })
        
        with open(results_file, "w") as f:
            json.dump(results_data, f, indent=2)
        
        print(f"\nDetailed results saved to {results_file}")
    
    print("Done!")
    return results

# Add a pytest-compatible test function
def test_embedding_retriever():
    """
    Pytest-compatible test for embedding retriever.
    This is a basic test that can be run with pytest to check if the system imports correctly.
    """
    # Create a simple memory store
    memory_dir = os.path.join(os.path.dirname(__file__), "test_data")
    os.makedirs(memory_dir, exist_ok=True)
    
    # Create a memory system instance
    memory = FewShotMemory(memory_dir=memory_dir, use_sqlite=True)
    
    # Basic assertions
    assert hasattr(memory, 'retrieve_memories'), "FewShotMemory should have retrieve_memories method"
    assert hasattr(memory, 'hybrid_retriever'), "FewShotMemory should have hybrid_retriever attribute"
    
    # Test passes if we get here
    return True

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Test memory retrieval system")
    parser.add_argument("--file", help="Path to code file to test")
    parser.add_argument("--code", help="Direct code input")
    parser.add_argument("--language", default="cpp", help="Programming language (cpp, python)")
    parser.add_argument("--memory-dir", help="Directory for memory storage")
    parser.add_argument("--verbose", "-v", action="store_true", help="Enable verbose output")
    parser.add_argument("--generate", "-g", action="store_true", help="Generate new test data")
    
    args = parser.parse_args()
    
    # Get code input
    code = args.code
    if args.file:
        with open(args.file, "r") as f:
            code = f.read()
    
    # Use default test if no code provided
    if not code:
        # Missing semicolon example
        code = """
#include <iostream>

int main() {
    int x = 5
    std::cout << "The value of x is: " << x << std::endl;
    return 0;
}
"""
        print("Using default test code (missing semicolon):")
        print(code)
    
    # Run test
    run_memory_retrieval(
        code=code,
        language=args.language,
        memory_dir=args.memory_dir,
        verbose=args.verbose,
        generate_data=args.generate
    )