# hagent/tool/memory/few_shot_memory_layer.py

# Set tokenizers parallelism to false to avoid warnings with forked processes
import os
os.environ["TOKENIZERS_PARALLELISM"] = "false"

import json
import os
import pickle
import sys
import re
import tempfile
import subprocess
import uuid
import numpy as np
from typing import List, Dict, Optional, Union, Tuple, Any
from datetime import datetime
from sentence_transformers import SentenceTransformer
from sklearn.metrics.pairwise import cosine_similarity
from pathlib import Path
from ruamel.yaml import YAML

from hagent.tool.memory.utils import normalize_code, CppBugExample, load_cpp_bugs_dataset
from hagent.tool.compile import Diagnostic

class Memory:
    """Basic memory unit with metadata"""
    def __init__(self, 
                 content: str,
                 id: Optional[str] = None,
                 keywords: Optional[List[str]] = None,
                 context: Optional[str] = None, 
                 tags: Optional[List[str]] = None,
                 timestamp: Optional[str] = None,
                 category: Optional[str] = None,
                 faulty_code: Optional[str] = None,
                 fixed_code: Optional[str] = None,
                 compiler_errors: Optional[List[str]] = None,
                 language: Optional[str] = None,
                 line_number: Optional[int] = None,
                 error_type: Optional[str] = None,
                 bug_category: Optional[str] = None,
                 embedding_text: Optional[str] = None):
        
        self.content = content
        self.id = id or str(uuid.uuid4())
        self.keywords = keywords or []
        self.timestamp = timestamp or datetime.now().strftime("%Y%m%d%H%M")
        
        # Handle context that can be either string or list
        self.context = context or "General"
        if isinstance(self.context, list):
            self.context = " ".join(self.context)
            
        self.category = category or "Uncategorized"
        self.tags = tags or []
        
        # C++ Bug specific attributes
        self.faulty_code = faulty_code
        self.fixed_code = fixed_code or ""
        self.compiler_errors = compiler_errors or []
        self.language = language or "cpp"
        self.line_number = line_number
        self.error_type = error_type or "unknown"
        self.bug_category = bug_category or "unknown"
        self.embedding_text = embedding_text or content
    
    @staticmethod
    def read_cpp_file(file_path):
        """Read C++ code from a file"""
        try:
            with open(file_path, 'r') as f:
                return f.read()
        except Exception as e:
            print(f"Error reading file {file_path}: {e}")
            return None
    
    @staticmethod
    def to_dict(item):
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
    
    @staticmethod
    def save_examples_to_yaml(matches, query_code, output_file, exact_match=False):
        """Save found examples to a YAML file"""
        # Create default output file if not provided
        if not output_file:
            results_dir = Path("results")
            results_dir.mkdir(exist_ok=True)
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            output_file = str(results_dir / f"matches_{timestamp}.yaml")
        
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
                "matches": [Memory.to_dict(match) for match in matches]
            }
        }
        
        # Save to YAML file
        yaml = YAML()
        yaml.indent(mapping=2, sequence=4, offset=2)
        with open(output_file, 'w') as f:
            yaml.dump(result, f)
        
        # print(f"\nResults saved to {output_file}")
    
    @staticmethod
    def initialize_paths(database_path: str) -> Tuple[Path, Path, Path]:
        """Initialize all necessary paths"""
        data_dir = Path("data")
        sample_db_path = Path(database_path)
        
        if not sample_db_path.exists():
            print(f"Error: Database file not found at {sample_db_path}")
            sys.exit(1)
        
        # Create a test output database so we don't modify the original
        test_db_path = data_dir / "test_memory_database.yaml"
        if test_db_path.exists():
            os.remove(test_db_path)  # Start fresh for the demo
            
        return data_dir, sample_db_path, test_db_path
    
    @staticmethod
    def setup_cache_directory(backend: str, model: str) -> Tuple[Path, Path]:
        """Set up cache directory for memories"""
        cache_dir = Path(f"cached_memories_{backend}_{model}")
        cache_dir.mkdir(exist_ok=True)
        memory_cache_file = cache_dir / "memory_cache_bugs.pkl"
        return cache_dir, memory_cache_file
    
    @staticmethod
    def load_or_create_memories(memory_system: 'FewShotMemory', 
                              memory_cache_file: Path, 
                              sample_db_path: Path) -> None:
        """Load memories from cache or create new ones if needed"""
        # Set the cache file path in the memory system
        memory_system.cache_file = str(memory_cache_file)
        
        # Try to load from cache first
        cache_loaded = False
        if memory_cache_file.exists():
            print(f"Loading cached memories from {memory_cache_file}")
            try:
                with open(memory_cache_file, 'rb') as f:
                    memory_system.memories = pickle.load(f)
                print(f"Successfully loaded {len(memory_system.memories)} memories from cache")
                cache_loaded = True
            except Exception as e:
                print(f"Error loading cached memories: {e}. Will try database.")
        
        # If cache loading failed, try database
        if not cache_loaded and sample_db_path.exists():
            print(f"Attempting to load from database at {sample_db_path}")
            try:
                # Load from database and then create cache
                memory_system.db_path = str(sample_db_path)
                memory_system.load_database()
                
                # Save to cache for next time
                print("Creating cache from database...")
                with open(memory_cache_file, 'wb') as f:
                    pickle.dump(memory_system.memories, f)
                print(f"Successfully cached {len(memory_system.memories)} memories")
                cache_loaded = True
            except Exception as e:
                print(f"Error loading from database: {e}. Will create new memories.")
        
        # If both failed, create new memories
        if not cache_loaded:
            print(f"No cached memories or database found. Creating new memories.")
            # Load examples from the original database
            cpp_bug_examples = load_cpp_bugs_dataset(sample_db_path)
            print(f"Loaded {len(cpp_bug_examples)} examples from {sample_db_path}")
            
            # Add examples to our memory system
            print(f"Adding examples to memory system...")
            for example in cpp_bug_examples:
                memory_system.add_from_example(example)
            
            # At this point, both database and cache should be updated by the add_from_example calls
    
    @staticmethod
    def process_matches(matches: List['Memory'], 
                       test_code: str, 
                       output_file: Optional[str] = None,
                       program_path: Optional[Path] = None) -> None:
        """Process and display matches found by the memory system"""
        exact_match = False
        
        # Determine output file path if not provided
        if program_path and not output_file:
            output_file = Memory.determine_output_file(output_file, program_path)
        
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
            Memory.save_examples_to_yaml(matches, test_code, output_file, exact_match)
        else:
            print("No similar examples found")
            Memory.save_examples_to_yaml([], test_code, output_file, False)
        
        print(f"Results saved to {output_file}")
    
    @staticmethod
    def save_databases(memory_system: 'FewShotMemory', 
                      test_db_path: Path, 
                      data_dir: Path) -> None:
        """Save memory databases in YAML and JSON formats"""
        print(f"\n--- Database statistics ---")
        print(f"Examples in memory: {len(memory_system.memories)}")
        
        # Save to YAML
        memory_system.save_database(str(test_db_path))
        # print(f"Saved to: {test_db_path}")
        
        # Save a copy in JSON format
        json_db_path = data_dir / "test_memory_database.json"
        if json_db_path.exists():
            os.remove(json_db_path)
        memory_system.save_database(str(json_db_path))
        # print(f"Also saved database in JSON format to: {json_db_path}")
    
    @staticmethod
    def determine_output_file(output_file: Optional[str], 
                             program_path: Path) -> str:
        """
        Determine the output file path, creates results directory if needed,
        and adds a timestamp to differentiate results of the same files.
        
        Args:
            output_file: Optional custom output file path
            program_path: Path of the input program file
            
        Returns:
            String path to the output file
        """
        if not output_file:
            # Create results directory if it doesn't exist
            results_dir = Path("results")
            results_dir.mkdir(exist_ok=True)
            
            # Add timestamp to filename to differentiate results of same files
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            file_name = program_path.stem
            output_file = str(results_dir / f"{file_name}_matches_{timestamp}.yaml")
        return output_file

    @staticmethod
    def detect_language(file_path):
        """Detect programming language from file extension."""
        extension = Path(file_path).suffix.lower()
        language_map = {
            '.cpp': 'C++',
            '.cc': 'C++',
            '.c': 'C',
            '.py': 'Python',
            '.v': 'Verilog',
            '.sv': 'SystemVerilog',
            '.js': 'JavaScript',
            '.ts': 'TypeScript',
            '.java': 'Java',
            '.go': 'Go',
            '.rb': 'Ruby',
            '.rs': 'Rust',
            '.scala': 'Chisel',
            '.pyrtl': 'PyRTL',
            '.vhdl': 'VHDL',
            '.vhd': 'VHDL',
            '.spade': 'Spade',
            '.sil': 'Silice'
        }
        return language_map.get(extension, 'Unknown')

    @staticmethod
    def get_language_code(language):
        """Convert full language name to code."""
        language_codes = {
            'C++': 'cpp',
            'C': 'c',
            'Python': 'python',
            'Verilog': 'verilog',
            'SystemVerilog': 'systemverilog',
            'JavaScript': 'js',
            'TypeScript': 'ts',
            'Java': 'java',
            'Go': 'go',
            'Ruby': 'ruby',
            'Rust': 'rust',
            'Chisel': 'chisel',
            'PyRTL': 'pyrtl',
            'VHDL': 'vhdl',
            'Spade': 'spade',
            'Silice': 'silice'
        }
        return language_codes.get(language, language.lower())

    @staticmethod
    def extract_bug_type(filename):
        """
        Try to extract bug type from filename as a fallback option.
        NOTE: This should not be the primary method to determine bug type,
        as filenames may not follow a standard pattern.
        """
        # Only attempt to extract from filename as a last resort
        match = re.search(r'(\d+)_([a-z_]+)_buggy', filename)
        if match:
            # Return with a note that this is from filename pattern matching
            bug_type = match.group(2).replace('_', ' ')
            return bug_type
        return "unknown bug"

    @staticmethod
    def get_compiler_errors(code: str, language: str, file_name: str) -> Tuple[List[str], Dict[str, Any], Optional[Diagnostic]]:
        """
        Compile the code and return errors and analysis.
        
        Args:
            code: The source code to compile
            language: The programming language
            file_name: Original file name for context
            
        Returns:
            Tuple of (error_messages, analysis_data, diagnostic)
        """
        errors = []
        analysis = {
            'error_type': 'unknown',
            'line_number': None,
            'severity': 'error',
            'description': '',
            'context': '',
            'specific_issue': '',
            'keywords': [],
            'tags': []
        }
        diagnostic = None
        
        if language == 'C++':
            with tempfile.NamedTemporaryFile(suffix='.cpp', delete=False) as tmp:
                tmp_path = tmp.name
                tmp.write(code.encode('utf-8'))
            
            try:
                # Try Clang++ for more detailed error messages
                try:
                    result = subprocess.run(['clang++', '-fsyntax-only', '-Wall', '-std=c++17', tmp_path], 
                                        capture_output=True, text=True, timeout=10)
                    
                    if result.returncode != 0:
                        # Use Diagnostic class to parse error messages
                        error_lines = [line for line in result.stderr.strip().split('\n') if line]
                        errors = error_lines
                        
                        # Parse error details using Diagnostic
                        if errors:
                            # Create a Diagnostic object from the first error line
                            diagnostic = Diagnostic(errors[0])
                            analysis['line_number'] = diagnostic.loc
                            analysis['severity'] = 'error' if diagnostic.error else 'warning'
                            analysis['description'] = diagnostic.msg
                            
                            # Determine error type based on message content
                            if "expected ';'" in diagnostic.msg:
                                analysis['error_type'] = 'missing_semicolon'
                                analysis['specific_issue'] = 'missing semicolon'
                            elif "use of undeclared identifier" in diagnostic.msg:
                                analysis['error_type'] = 'undeclared_variable'
                                analysis['specific_issue'] = 'undeclared variable'
                            elif "expected ')'" in diagnostic.msg or "expected '}'" in diagnostic.msg:
                                analysis['error_type'] = 'mismatched_brackets'
                                analysis['specific_issue'] = 'mismatched brackets or parentheses'
                            elif "null pointer" in diagnostic.msg or "dereference" in diagnostic.msg:
                                analysis['error_type'] = 'null_pointer'
                                analysis['specific_issue'] = 'null pointer dereference'
                            elif "array" in diagnostic.msg and ("bounds" in diagnostic.msg or "initialization" in diagnostic.msg):
                                analysis['error_type'] = 'array_bounds'
                                analysis['specific_issue'] = 'array bounds or initialization issue'
                            elif "leak" in diagnostic.msg or ("new" in diagnostic.msg and "delete" in diagnostic.msg):
                                analysis['error_type'] = 'memory_leak'
                                analysis['specific_issue'] = 'memory leak or allocation issue'
                            elif "division" in diagnostic.msg or "operator" in diagnostic.msg:
                                analysis['error_type'] = 'operator_error'
                                analysis['specific_issue'] = 'incorrect operator usage'
                            elif "shadow" in diagnostic.msg:
                                analysis['error_type'] = 'variable_shadowing'
                                analysis['specific_issue'] = 'variable shadowing'
                            elif "uninitialized" in diagnostic.msg:
                                analysis['error_type'] = 'uninitialized_variable'
                                analysis['specific_issue'] = 'uninitialized variable'
                            else:
                                # Keep error type as 'unknown' if we can't determine it from the error message
                                analysis['error_type'] = 'syntax_error'
                                analysis['specific_issue'] = 'syntax error'
                        
                        # Get context from code
                        if analysis['line_number']:
                            lines = code.split('\n')
                            if 0 <= analysis['line_number']-1 < len(lines):
                                analysis['context'] = lines[analysis['line_number']-1].strip()
                except (FileNotFoundError, subprocess.TimeoutExpired):
                    # Try GCC instead
                    try:
                        result = subprocess.run(['g++', '-fsyntax-only', '-Wall', '-std=c++17', tmp_path], 
                                            capture_output=True, text=True, timeout=10)
                        
                        if result.returncode != 0:
                            errors = [line for line in result.stderr.strip().split('\n') if line]
                            
                            # Use Diagnostic if there are errors
                            if errors:
                                diagnostic = Diagnostic(errors[0])
                                analysis['line_number'] = diagnostic.loc
                                analysis['severity'] = 'error' if diagnostic.error else 'warning'
                                analysis['description'] = diagnostic.msg
                    except (FileNotFoundError, subprocess.TimeoutExpired):
                        # Fallback: basic analysis from code
                        err_msg = "Could not compile code - compiler not available"
                        errors.append(err_msg)
                        analysis['description'] = err_msg
            
            finally:
                if os.path.exists(tmp_path):
                    os.remove(tmp_path)
        
        elif language == 'Python':
            with tempfile.NamedTemporaryFile(suffix='.py', delete=False) as tmp:
                tmp_path = tmp.name
                tmp.write(code.encode('utf-8'))
            
            try:
                # Check syntax errors
                result = subprocess.run([sys.executable, '-m', 'py_compile', tmp_path], 
                                    capture_output=True, text=True, timeout=10)
                
                if result.returncode != 0:
                    error_lines = [line for line in result.stderr.strip().split('\n') if line]
                    errors = error_lines
                    
                    # Parse Python errors
                    if errors:
                        # Use a custom approach for Python errors since they don't match the format Diagnostic expects
                        match = re.search(r'File ".*", line (\d+)', errors[0])
                        if match:
                            analysis['line_number'] = int(match.group(1))
                        
                        if "SyntaxError" in errors[-1]:
                            analysis['error_type'] = 'syntax_error'
                            analysis['specific_issue'] = 'syntax error'
                            # Get the specific error message
                            match = re.search(r'SyntaxError: (.+)', errors[-1])
                            if match:
                                analysis['description'] = match.group(1)
            except Exception as e:
                errors.append(f"Error analyzing Python code: {str(e)}")
            finally:
                if os.path.exists(tmp_path):
                    os.remove(tmp_path)
        
        elif language in ['Verilog', 'SystemVerilog']:
            # Verilog/SystemVerilog implementation using Icarus Verilog
            suffix = '.v' if language == 'Verilog' else '.sv'
            with tempfile.NamedTemporaryFile(suffix=suffix, delete=False) as tmp:
                tmp_path = tmp.name
                tmp.write(code.encode('utf-8'))
            
            try:
                # Use iverilog for compilation checking
                result = subprocess.run(['iverilog', '-t', 'null', tmp_path], 
                                    capture_output=True, text=True, timeout=10)
                
                if result.returncode != 0:
                    error_lines = [line for line in result.stderr.strip().split('\n') if line]
                    errors = error_lines
                    
                    # Parse Verilog errors
                    if errors:
                        # Extract line number if available
                        line_match = re.search(r':(\d+):', errors[0])
                        if line_match:
                            analysis['line_number'] = int(line_match.group(1))
                        
                        # Determine error type
                        error_msg = errors[0].lower()
                        if "syntax error" in error_msg:
                            analysis['error_type'] = 'syntax_error'
                            analysis['specific_issue'] = 'syntax error'
                        elif "undeclared" in error_msg:
                            analysis['error_type'] = 'undeclared_symbol'
                            analysis['specific_issue'] = 'undeclared symbol'
                        elif "mismatch" in error_msg:
                            analysis['error_type'] = 'type_mismatch'
                            analysis['specific_issue'] = 'type mismatch'
                        elif "assign" in error_msg and "wire" in error_msg:
                            analysis['error_type'] = 'wire_assignment'
                            analysis['specific_issue'] = 'invalid wire assignment'
                        elif "width" in error_msg:
                            analysis['error_type'] = 'width_mismatch'
                            analysis['specific_issue'] = 'bus width mismatch'
                        else:
                            analysis['error_type'] = 'verilog_error'
                            analysis['specific_issue'] = 'verilog compilation error'
                        
                        # Set description
                        analysis['description'] = errors[0]
                        
                        # Get context
                        if analysis['line_number']:
                            lines = code.split('\n')
                            if 0 <= analysis['line_number']-1 < len(lines):
                                analysis['context'] = lines[analysis['line_number']-1].strip()
                
                # Try verilator as an additional check if iverilog doesn't find errors
                if not errors:
                    try:
                        result = subprocess.run(['verilator', '--lint-only', '-Wall', tmp_path], 
                                            capture_output=True, text=True, timeout=10)
                        if result.returncode != 0:
                            error_lines = [line for line in result.stderr.strip().split('\n') if line]
                            errors = error_lines
                            
                            # Basic parsing - verilator has a different format
                            if errors:
                                for line in errors:
                                    if "ERROR" in line:
                                        line_match = re.search(r':(\d+):', line)
                                        if line_match:
                                            analysis['line_number'] = int(line_match.group(1))
                                        analysis['description'] = line
                                        analysis['error_type'] = 'verilog_error'
                                        analysis['specific_issue'] = 'verilog compilation error'
                                        break
                    except (FileNotFoundError, subprocess.TimeoutExpired):
                        pass  # Verilator not available, continue with iverilog results
            
            except (FileNotFoundError, subprocess.TimeoutExpired):
                errors.append(f"Verilog compilation tools not available")
                analysis['description'] = "Could not find Verilog compilation tools (iverilog/verilator)"
            
            finally:
                if os.path.exists(tmp_path):
                    os.remove(tmp_path)
        
        elif language == 'VHDL':
            # VHDL implementation with GHDL
            with tempfile.NamedTemporaryFile(suffix='.vhd', delete=False) as tmp:
                tmp_path = tmp.name
                tmp.write(code.encode('utf-8'))
            
            try:
                # Use GHDL for syntax checking
                result = subprocess.run(['ghdl', '-s', '--std=08', tmp_path], 
                                    capture_output=True, text=True, timeout=10)
                
                if result.returncode != 0:
                    error_lines = [line for line in result.stderr.strip().split('\n') if line]
                    errors = error_lines
                    
                    # Parse VHDL errors
                    if errors:
                        # Extract line number if available
                        line_match = re.search(r':(\d+):(\d+):', errors[0])
                        if line_match:
                            analysis['line_number'] = int(line_match.group(1))
                        
                        # Determine error type
                        error_msg = errors[0].lower()
                        if "expect" in error_msg and "found" in error_msg:
                            analysis['error_type'] = 'syntax_error'
                            analysis['specific_issue'] = 'syntax error'
                        elif "no declaration" in error_msg:
                            analysis['error_type'] = 'undeclared_symbol'
                            analysis['specific_issue'] = 'undeclared symbol'
                        elif "already declared" in error_msg:
                            analysis['error_type'] = 'redeclaration'
                            analysis['specific_issue'] = 'symbol already declared'
                        elif "type mismatch" in error_msg:
                            analysis['error_type'] = 'type_mismatch'
                            analysis['specific_issue'] = 'type mismatch'
                        elif "missing" in error_msg:
                            analysis['error_type'] = 'missing_element'
                            analysis['specific_issue'] = 'missing element'
                        else:
                            analysis['error_type'] = 'vhdl_error'
                            analysis['specific_issue'] = 'VHDL compilation error'
                        
                        # Set description
                        analysis['description'] = errors[0]
                        
                        # Get context
                        if analysis['line_number']:
                            lines = code.split('\n')
                            if 0 <= analysis['line_number']-1 < len(lines):
                                analysis['context'] = lines[analysis['line_number']-1].strip()
            
            except (FileNotFoundError, subprocess.TimeoutExpired):
                errors.append("VHDL compilation tools not available")
                analysis['description'] = "Could not find VHDL compilation tools (GHDL)"
            
            finally:
                if os.path.exists(tmp_path):
                    os.remove(tmp_path)
        
        elif language == 'Chisel':
            # Chisel (Scala-based HDL) using the Scala compiler
            with tempfile.NamedTemporaryFile(suffix='.scala', delete=False) as tmp:
                tmp_path = tmp.name
                tmp.write(code.encode('utf-8'))
            
            try:
                # Use scalac for basic syntax checking
                result = subprocess.run(['scalac', tmp_path], 
                                    capture_output=True, text=True, timeout=15)
                
                if result.returncode != 0:
                    error_lines = [line for line in result.stderr.strip().split('\n') if line]
                    errors = error_lines
                    
                    # Parse Scala errors
                    if errors:
                        # Extract line number
                        line_match = re.search(r':(\d+):', errors[0])
                        if line_match:
                            analysis['line_number'] = int(line_match.group(1))
                        
                        # Determine error type
                        error_msg = ' '.join(errors).lower()
                        if "not found" in error_msg:
                            analysis['error_type'] = 'symbol_not_found'
                            analysis['specific_issue'] = 'symbol not found'
                        elif "expected" in error_msg and (";" in error_msg or "{" in error_msg or "}" in error_msg):
                            analysis['error_type'] = 'syntax_error'
                            analysis['specific_issue'] = 'syntax error'
                        elif "type mismatch" in error_msg:
                            analysis['error_type'] = 'type_mismatch'
                            analysis['specific_issue'] = 'type mismatch'
                        elif "overloaded" in error_msg:
                            analysis['error_type'] = 'overloaded_method'
                            analysis['specific_issue'] = 'ambiguous method overload'
                        elif "class not found" in error_msg or "object not found" in error_msg:
                            analysis['error_type'] = 'module_connection'
                            analysis['specific_issue'] = 'module connection error'
                        else:
                            analysis['error_type'] = 'chisel_error'
                            analysis['specific_issue'] = 'chisel compilation error'
                        
                        # Set description
                        analysis['description'] = errors[0]
                        
                        # Get context
                        if analysis['line_number']:
                            lines = code.split('\n')
                            if 0 <= analysis['line_number']-1 < len(lines):
                                analysis['context'] = lines[analysis['line_number']-1].strip()
            
            except (FileNotFoundError, subprocess.TimeoutExpired):
                errors.append("Scala/Chisel compilation tools not available")
                analysis['description'] = "Could not find Scala compilation tools"
            
            finally:
                if os.path.exists(tmp_path):
                    os.remove(tmp_path)
        
        elif language == 'PyRTL':
            # PyRTL is Python-based, so we use Python's error detection and custom checks
            with tempfile.NamedTemporaryFile(suffix='.py', delete=False) as tmp:
                tmp_path = tmp.name
                # Add PyRTL import at the top if not already present
                if "import pyrtl" not in code.lower():
                    tmp.write(b"import pyrtl\n")
                tmp.write(code.encode('utf-8'))
                tmp.flush()
            
            try:
                # First check Python syntax
                py_result = subprocess.run([sys.executable, '-m', 'py_compile', tmp_path], 
                                       capture_output=True, text=True, timeout=10)
                
                if py_result.returncode != 0:
                    # Python syntax error
                    error_lines = [line for line in py_result.stderr.strip().split('\n') if line]
                    errors = error_lines
                    
                    # Parse Python errors as before
                    if errors:
                        match = re.search(r'File ".*", line (\d+)', errors[0])
                        if match:
                            analysis['line_number'] = int(match.group(1))
                        
                        analysis['error_type'] = 'syntax_error'
                        analysis['specific_issue'] = 'syntax error'
                        analysis['description'] = errors[-1] if errors else "Syntax error in PyRTL code"
                
                else:
                    # Try to actually run the PyRTL code to check for PyRTL-specific errors
                    try:
                        # Run with a timeout
                        run_result = subprocess.run([sys.executable, tmp_path], 
                                       capture_output=True, text=True, timeout=10)
                        
                        if run_result.returncode != 0:
                            # PyRTL execution error
                            error_lines = [line for line in run_result.stderr.strip().split('\n') if line]
                            errors = error_lines
                            
                            # Parse PyRTL-specific errors
                            if errors:
                                # Extract line number if available
                                line_match = re.search(r'line (\d+)', ' '.join(errors))
                                if line_match:
                                    analysis['line_number'] = int(line_match.group(1))
                                
                                # Determine error type
                                error_text = ' '.join(errors).lower()
                                if "wirevector" in error_text:
                                    analysis['error_type'] = 'wire_error'
                                    analysis['specific_issue'] = 'invalid wire operation'
                                elif "assignment" in error_text:
                                    analysis['error_type'] = 'wire_assignment'
                                    analysis['specific_issue'] = 'invalid wire assignment'
                                elif "block" in error_text and "error" in error_text:
                                    analysis['error_type'] = 'block_error'
                                    analysis['specific_issue'] = 'block instantiation error'
                                else:
                                    analysis['error_type'] = 'pyrtl_error'
                                    analysis['specific_issue'] = 'PyRTL execution error'
                                
                                analysis['description'] = errors[0] if errors else "Error in PyRTL code"
                    
                    except subprocess.TimeoutExpired:
                        errors.append("PyRTL execution timed out (possible infinite loop)")
                        analysis['error_type'] = 'timeout'
                        analysis['specific_issue'] = 'execution timeout'
                        analysis['description'] = "PyRTL execution timed out - possible infinite loop"
            
            except Exception as e:
                errors.append(f"Error analyzing PyRTL code: {str(e)}")
                analysis['description'] = f"Error analyzing PyRTL code: {str(e)}"
            
            finally:
                if os.path.exists(tmp_path):
                    os.remove(tmp_path)
        
        elif language == 'Spade':
            # Spade hardware description language
            with tempfile.NamedTemporaryFile(suffix='.spade', delete=False) as tmp:
                tmp_path = tmp.name
                tmp.write(code.encode('utf-8'))
            
            try:
                # Use a simple regex-based approach to identify common Spade errors
                # since the compiler might not be available in many environments
                
                # Check for missing parentheses
                paren_errors = []
                open_parens = code.count('(')
                close_parens = code.count(')')
                if open_parens > close_parens:
                    paren_errors.append(f"Missing {open_parens - close_parens} closing parentheses ')'")
                elif close_parens > open_parens:
                    paren_errors.append(f"Missing {close_parens - open_parens} opening parentheses '('")
                
                # Check for missing braces
                brace_errors = []
                open_braces = code.count('{')
                close_braces = code.count('}')
                if open_braces > close_braces:
                    brace_errors.append(f"Missing {open_braces - close_braces} closing braces '}}'")
                elif close_braces > open_braces:
                    brace_errors.append(f"Missing {close_braces - open_braces} opening braces '{{'")
                
                # Check for common Spade keywords
                if "Accel" not in code and "Kernel" not in code and "Module" not in code:
                    errors.append("Missing Spade component declaration (Accel/Kernel/Module)")
                    analysis['error_type'] = 'missing_component'
                    analysis['specific_issue'] = 'missing component declaration'
                    analysis['description'] = "No Accel, Kernel or Module declaration found"
                
                # Add any parenthesis/brace errors
                if paren_errors or brace_errors:
                    errors.extend(paren_errors)
                    errors.extend(brace_errors)
                    analysis['error_type'] = 'missing_parenthesis'
                    analysis['specific_issue'] = 'missing parentheses or braces'
                    analysis['description'] = '; '.join(paren_errors + brace_errors)
                
                # Check for undefined variables using a simple pattern
                lines = code.split('\n')
                for i, line in enumerate(lines):
                    # Look for variable assignments
                    if '=' in line and 'val' not in line and 'var' not in line:
                        var_name = line.split('=')[0].strip()
                        # Check if this variable is defined previously
                        is_defined = False
                        for prev_line in lines[:i]:
                            if f"val {var_name}" in prev_line or f"var {var_name}" in prev_line:
                                is_defined = True
                                break
                        
                        if not is_defined and not var_name.startswith("_"):
                            errors.append(f"Potentially undefined variable: {var_name} at line {i+1}")
                            analysis['error_type'] = 'undefined_variable'
                            analysis['specific_issue'] = 'undefined variable'
                            analysis['description'] = f"Variable '{var_name}' might be undefined"
                            analysis['line_number'] = i+1
                            analysis['context'] = line.strip()
                            break
                
                # Try to run the Spade compiler if available
                try:
                    # This assumes a 'spade' command is available
                    result = subprocess.run(['spade', 'check', tmp_path], 
                                        capture_output=True, text=True, timeout=15)
                    
                    if result.returncode != 0:
                        error_lines = [line for line in result.stderr.strip().split('\n') if line]
                        if error_lines:
                            errors = error_lines  # Replace heuristic errors with actual compiler errors
                            
                            # Extract line number if available
                            line_match = re.search(r':(\d+):', error_lines[0])
                            if line_match:
                                analysis['line_number'] = int(line_match.group(1))
                            
                            analysis['description'] = error_lines[0]
                            
                            # Update context if line number found
                            if analysis['line_number']:
                                if 0 <= analysis['line_number']-1 < len(lines):
                                    analysis['context'] = lines[analysis['line_number']-1].strip()
                
                except (FileNotFoundError, subprocess.TimeoutExpired):
                    # Spade compiler not available, continue with heuristic analysis
                    if not errors:
                        errors.append("Spade analysis performed without compiler - potential errors might be missed")
            
            except Exception as e:
                errors.append(f"Error analyzing Spade code: {str(e)}")
                analysis['description'] = f"Error analyzing Spade code: {str(e)}"
            
            finally:
                if os.path.exists(tmp_path):
                    os.remove(tmp_path)
        
        elif language == 'Silice':
            # Silice hardware description language
            with tempfile.NamedTemporaryFile(suffix='.sil', delete=False) as tmp:
                tmp_path = tmp.name
                tmp.write(code.encode('utf-8'))
            
            try:
                # Use heuristic analysis for Silice
                errors = []
                
                # Check for semicolons
                lines = code.split('\n')
                for i, line in enumerate(lines):
                    # Remove comments
                    line = re.sub(r'//.*$', '', line)
                    
                    # Skip empty lines or lines that don't need semicolons
                    if not line.strip() or line.strip().endswith('{') or line.strip().endswith('}'):
                        continue
                    
                    # Check if line needs a semicolon
                    if (not line.strip().endswith(';') and 
                        not line.strip().endswith(')') and
                        not line.strip().endswith('else') and
                        not line.strip().startswith('algorithm') and
                        not line.strip().startswith('else') and
                        not line.strip().startswith('if') and
                        not line.strip().startswith('while')):
                        
                        errors.append(f"Missing semicolon at line {i+1}: {line.strip()}")
                        analysis['error_type'] = 'missing_semicolon'
                        analysis['specific_issue'] = 'missing semicolon'
                        analysis['description'] = f"Line might be missing a semicolon"
                        analysis['line_number'] = i+1
                        analysis['context'] = line.strip()
                        break
                
                # Check for algorithm definition
                if 'algorithm' not in code:
                    errors.append("No 'algorithm' definition found in Silice code")
                    analysis['error_type'] = 'missing_algorithm'
                    analysis['specific_issue'] = 'missing algorithm definition'
                    analysis['description'] = "No algorithm definition found"
                
                # Check for brace matching
                open_braces = code.count('{')
                close_braces = code.count('}')
                if open_braces != close_braces:
                    diff = abs(open_braces - close_braces)
                    if open_braces > close_braces:
                        msg = f"Missing {diff} closing braces '}}'"
                    else:
                        msg = f"Missing {diff} opening braces '{{'"
                    
                    errors.append(msg)
                    analysis['error_type'] = 'mismatched_brackets'
                    analysis['specific_issue'] = 'mismatched braces'
                    analysis['description'] = msg
                
                # Try to run the Silice compiler if available
                try:
                    # This assumes a 'silice' command is available
                    result = subprocess.run(['silice', '--check', tmp_path], 
                                        capture_output=True, text=True, timeout=15)
                    
                    if result.returncode != 0:
                        error_lines = [line for line in result.stderr.strip().split('\n') if line]
                        if error_lines:
                            errors = error_lines  # Replace heuristic errors with actual compiler errors
                            
                            # Extract line number if available
                            line_match = re.search(r'line (\d+)', ' '.join(error_lines))
                            if line_match:
                                analysis['line_number'] = int(line_match.group(1))
                            
                            analysis['description'] = error_lines[0]
                            
                            # Update context if line number found
                            if analysis['line_number']:
                                if 0 <= analysis['line_number']-1 < len(lines):
                                    analysis['context'] = lines[analysis['line_number']-1].strip()
                
                except (FileNotFoundError, subprocess.TimeoutExpired):
                    # Silice compiler not available, continue with heuristic analysis
                    if not errors:
                        errors.append("Silice analysis performed without compiler - potential errors might be missed")
            
            except Exception as e:
                errors.append(f"Error analyzing Silice code: {str(e)}")
                analysis['description'] = f"Error analyzing Silice code: {str(e)}"
            
            finally:
                if os.path.exists(tmp_path):
                    os.remove(tmp_path)
        
        # Generate keywords and tags based on analysis
        base_keywords = [language]
        base_tags = [Memory.get_language_code(language), 'debugging']
        
        if analysis['specific_issue']:
            keywords = base_keywords + [analysis['specific_issue'], 'bug', analysis['severity']]
            if 'error_type' in analysis and analysis['error_type'] != 'unknown':
                tags = base_tags + [analysis['error_type'].replace('_', ' ')]
                if any(category in analysis['error_type'] for category in ['pointer', 'memory', 'leak']):
                    tags.append('memory management')
                elif any(category in analysis['error_type'] for category in ['syntax', 'semicolon', 'brackets']):
                    tags.append('syntax')
                elif any(category in analysis['error_type'] for category in ['variable', 'uninitialized']):
                    tags.append('variables')
                elif any(category in analysis['error_type'] for category in ['wire', 'assignment', 'width']):
                    tags.append('hdl wiring')
                elif any(category in analysis['error_type'] for category in ['module', 'connection']):
                    tags.append('module connection')
            else:
                tags = base_tags
        else:
            keywords = base_keywords + ['bug']
            tags = base_tags
        
        analysis['keywords'] = list(set(keywords))
        analysis['tags'] = list(set(tags))
        
        # If no errors found but we expect there to be errors
        if not errors and '_buggy' in file_name:
            generic_error = f"Code contains errors not detected by automatic analysis"
            errors.append(generic_error)
            if not analysis['description']:
                analysis['description'] = generic_error
        
        # Create a diagnostic from the errors
        if errors:
            error_msg = errors[0]
            diagnostic = Diagnostic(error_msg)
            diagnostic.file = file_name
            diagnostic.loc = analysis['line_number'] or 0
            diagnostic.error = analysis['severity'] == 'error'
            if len(errors) > 1:
                diagnostic.hint = '\n'.join(errors[1:])
        else:
            # Create an empty diagnostic
            diagnostic = Diagnostic("")
            diagnostic.file = file_name
        
        return errors, analysis, diagnostic

    @staticmethod
    def generate_bug_description(analysis, bug_number, file_name):
        """Generate a human-readable bug description based on error analysis."""
        
        # Generate description based primarily on analysis results
        if analysis.get('description') and analysis.get('specific_issue'):
            description = f"Fix the {analysis['specific_issue']} in this code. Error: {analysis['description']}"
        elif analysis.get('description'):
            description = f"Fix the code error: {analysis['description']}"
        elif analysis.get('specific_issue'):
            description = f"Fix the {analysis['specific_issue']} in this code."
        else:
            # Fallback - generic description without attempting to extract from filename
            description = f"Fix the bug in this code (Bug #{bug_number})."
        
        return description

    @staticmethod
    def read_code_file(file_path):
        """Read code from a file."""
        try:
            with open(file_path, 'r') as f:
                return f.read()
        except Exception as e:
            print(f"Error reading file {file_path}: {str(e)}")
            return ""

class FewShotMemory:
    """Simple memory system with embedding-based retrieval for C++ code bug examples"""
    
    def __init__(self, 
                 db_path: str = "data/sample_memories.yaml", 
                 model_name: str = "all-MiniLM-L6-v2",
                 cache_file: str = None,
                 auto_create_data: bool = True,
                 programs_path: str = None):
        """Initialize the memory system
        
        Args:
            db_path: Path to the database file
            model_name: Name of the sentence transformer model
            cache_file: Path to the cache file
            auto_create_data: Whether to automatically create test data if database doesn't exist
            programs_path: Path to the directory containing program examples
        """
        # Set up paths and directories
        # Create data directory and set up database path
        data_dir = Path("data")
        data_dir.mkdir(exist_ok=True)
        self.db_path = str(Path(db_path)) if not isinstance(db_path, Path) else str(db_path)
        
        # Set up cache directory for memories
        if cache_file is None:
            cache_dir = Path("cached_memories")
            cache_dir.mkdir(exist_ok=True)
            self.cache_file = str(cache_dir / "memory_cache_bugs.pkl")
        else:
            cache_file_path = Path(cache_file) if not isinstance(cache_file, Path) else cache_file
            cache_file_path.parent.mkdir(exist_ok=True)
            self.cache_file = str(cache_file_path)
        
        self.model = SentenceTransformer(model_name)
        self.memories = {}  # Stores Memory objects by ID
        
        # CHANGED: First try to load from cache, then fallback to database
        cache_loaded = self._try_load_from_cache()
        
        # If cache loading failed, try to load from database
        if not cache_loaded:
            print(f"Cache loading failed or not available. Trying database...")
            database_loaded = self._try_load_from_database()
            
            # If neither cache nor database worked and auto_create_data is enabled, create data
            if not database_loaded and auto_create_data:
                print(f"Database not found at {self.db_path}. Creating test data...")
                
                # Create test data
                json_path, yaml_path = self.create_sample_data(
                    programs_path=programs_path,
                    output_path=self.db_path.replace('.yaml', '.json').replace('.yml', '.json'),
                    output_yaml_path=self.db_path,
                    create_embeddings=True
                )
                
                if json_path and yaml_path:
                    print(f"Created test data at {json_path} and {yaml_path}")
                    # Save to cache for faster loading next time
                    print("Creating cache from new database...")
                    self._save_to_cache()
    
    def _try_load_from_cache(self) -> bool:
        """
        Try to load memories from cache file
        
        Returns:
            bool: True if successfully loaded from cache, False otherwise
        """
        if os.path.exists(self.cache_file):
            try:
                print(f"Loading memories from cache file: {self.cache_file}")
                with open(self.cache_file, 'rb') as f:
                    self.memories = pickle.load(f)
                print(f"Successfully loaded {len(self.memories)} memories from cache")
                return True
            except Exception as e:
                print(f"Error loading from cache: {e}")
        return False

    def _try_load_from_database(self) -> bool:
        """
        Try to load memories from database file
        
        Returns:
            bool: True if successfully loaded from database, False otherwise
        """
        if os.path.exists(self.db_path):
            try:
                print(f"Loading memories from database: {self.db_path}")
                # Use existing load_database logic with a return value
                self.load_database()
                if self.memories:
                    print(f"Successfully loaded {len(self.memories)} memories from database")
                    # After loading from database, update the cache for faster future loads
                    self._save_to_cache()
                    return True
            except Exception as e:
                print(f"Error loading from database: {e}")
        return False

    def _save_to_cache(self) -> None:
        """Save current memories to cache file"""
        if not self.memories:
            print("No memories to cache")
            return
        
        try:
            print(f"Saving {len(self.memories)} memories to cache: {self.cache_file}")
            with open(self.cache_file, 'wb') as f:
                pickle.dump(self.memories, f)
            print(f"Successfully cached {len(self.memories)} memories")
        except Exception as e:
            print(f"Error saving to cache: {e}")

    def load_database(self) -> bool:
        """Load memories from database (JSON or YAML) if it exists"""
        if not os.path.exists(self.db_path):
            print(f"No existing database found at {self.db_path}")
            return False
            
        try:
            # Get file extension to determine format
            path = Path(self.db_path)
            suffix = path.suffix.lower()
            
            if suffix == '.json':
                with open(self.db_path, 'r') as f:
                    data = json.load(f)
            elif suffix in ['.yaml', '.yml']:
                yaml = YAML(typ='safe')
                with open(self.db_path, 'r') as f:
                    data = yaml.load(f)
            else:
                raise ValueError(f"Unsupported file format: {suffix}. Expected .json, .yaml, or .yml")
            
            # Convert data to Memory objects
            for item in data:
                # Load embedding if available
                embedding = None
                if "embedding" in item and item["embedding"]:
                    embedding = np.array(item["embedding"])
                
                memory_item = Memory(
                    id=item["id"],
                    content=item["content"],
                    keywords=item.get("keywords", []),
                    context=item.get("context", "C++ bug"),
                    tags=item.get("tags", []),
                    timestamp=item.get("timestamp"),
                    category=item.get("category", "C++"),
                    faulty_code=item.get("faulty_code", ""),
                    fixed_code=item.get("fixed_code", ""),
                    compiler_errors=item.get("compiler_errors", []),
                    language=item.get("language", "cpp"),
                    line_number=item.get("line_number"),
                    error_type=item.get("error_type", "unknown"),
                    bug_category=item.get("bug_category", "unknown"),
                    embedding_text=item.get("embedding_text", "")
                )
                
                # Add embedding to memory object
                if embedding is not None:
                    memory_item.embedding = embedding
                
                self.memories[memory_item.id] = memory_item
            
            print(f"Loaded {len(self.memories)} items from database at {self.db_path}")
            return True
        except Exception as e:
            print(f"Error loading database: {e}")
            self.memories = {}
            return False
    
    def save_database(self, output_path: Optional[str] = None) -> None:
        """Save memories to database (JSON or YAML)"""
        if output_path is None:
            output_path = self.db_path
            
        path = Path(output_path)
        memory_list = []
        
        # Create directory if it doesn't exist
        os.makedirs(path.parent, exist_ok=True)
        
        # Convert Memory objects to dictionaries
        for memory in self.memories.values():
            # Generate embedding if not already present
            embedding_text = getattr(memory, 'embedding_text', memory.faulty_code)
            if not hasattr(memory, 'embedding') or memory.embedding is None:
                memory.embedding = self.model.encode([embedding_text])[0]
                
            item = {
                "id": memory.id,
                "content": memory.content,
                "keywords": memory.keywords,
                "context": memory.context,
                "tags": memory.tags,
                "timestamp": memory.timestamp,
                "category": memory.category,
                "faulty_code": memory.faulty_code,
                "fixed_code": memory.fixed_code,
                "compiler_errors": memory.compiler_errors,
                "language": getattr(memory, "language", "cpp"),
                "line_number": getattr(memory, "line_number", None),
                "error_type": getattr(memory, "error_type", "unknown"),
                "bug_category": getattr(memory, "bug_category", "unknown"),
                "embedding_text": embedding_text,
                "embedding": memory.embedding.tolist() if hasattr(memory, 'embedding') and memory.embedding is not None else []
            }
            memory_list.append(item)
        
        # Save based on file extension
        suffix = path.suffix.lower()
        try:
            if suffix == '.json':
                with open(output_path, 'w') as f:
                    json.dump(memory_list, f, indent=2)
            elif suffix in ['.yaml', '.yml']:
                yaml = YAML()
                yaml.indent(mapping=2, sequence=4, offset=2)
                with open(output_path, 'w') as f:
                    yaml.dump(memory_list, f)
            else:
                with open(output_path, 'w') as f:
                    json.dump(memory_list, f, indent=2)
            
            # print(f"Saved {len(self.memories)} items to database at {output_path}")
        except Exception as e:
            print(f"Error saving database to {output_path}: {e}")
    
    def add(self, err: Diagnostic, fix_question: str, fix_answer: str = None) -> str:
        """
        Add a new memory item using Diagnostic object
        
        Args:
            err: Diagnostic object containing error information
            fix_question: The code with the error (faulty code)
            fix_answer: The fixed code (if available)
            
        Returns:
            String ID of the newly created memory
        """
        # Extract error information from Diagnostic
        error_type = "unknown"
        bug_category = "unknown"
        line_number = err.loc if hasattr(err, 'loc') else None
        compiler_errors = [err.msg] if hasattr(err, 'msg') and err.msg else []
        
        # Determine error type from Diagnostic message
        if hasattr(err, 'msg') and err.msg:
            error_msg = err.msg.lower()
            if "syntax" in error_msg:
                error_type = "syntax_error"
            elif "undefined" in error_msg or "undeclared" in error_msg:
                error_type = "undefined_symbol"
            elif "redefinition" in error_msg or "redeclared" in error_msg:
                error_type = "redefinition_error"
            elif "expected" in error_msg:
                error_type = "missing_element"
            elif "semicolon" in error_msg:
                error_type = "missing_semicolon"
            elif "brackets" in error_msg or "parenthesis" in error_msg or "brace" in error_msg:
                error_type = "mismatched_brackets"
        
        # Categorize the bug
        if any(kw in error_msg for kw in ["memory", "allocation", "free", "leak"]):
            bug_category = "memory_management"
        elif any(kw in error_msg for kw in ["type", "conversion"]):
            bug_category = "type_error"
        elif any(kw in error_msg for kw in ["syntax", "token", "expected"]):
            bug_category = "syntax"
        elif any(kw in error_msg for kw in ["wire", "port", "connection"]):
            bug_category = "hdl_wiring"
    
        # Generate a content description
        content = f"Bug: Fix the {error_type if error_type != 'unknown' else 'bug'} in this code."
        
        if hasattr(err, 'msg') and err.msg:
            content += f" Error: {err.msg}"
        
        # Get the language from the file or code content
        language = "cpp"  # Default
        if hasattr(err, 'file') and err.file:
            language_from_file = Memory.detect_language(Path(err.file))
            if language_from_file != 'Unknown':
                language = Memory.get_language_code(language_from_file)
        
        # Create memory item
        memory_id = str(uuid.uuid4())
        memory_item = Memory(
            id=memory_id,
            content=content,
            keywords=[language, error_type, "error", "bug"],
            context=f"{language} programming bug fix: {error_type}",
            tags=["debugging", error_type.replace('_', ' '), language],
            timestamp=datetime.now().strftime("%Y%m%d%H%M"),
            category=language.upper(),
            faulty_code=fix_question,
            fixed_code=fix_answer,
            compiler_errors=compiler_errors,
            language=language,
            line_number=line_number,
            error_type=error_type,
            bug_category=bug_category,
            embedding_text=f"{language} programming bug fix: {error_type} {fix_question}"
        )
        
        # Add to memories
        self.memories[memory_id] = memory_item
        
        # Update both database and cache
        print(f"Adding new memory with ID: {memory_id}")
        
        # Save to database first
        self.save_database()
        
        # Then save to cache - this is now the primary storage
        self._save_to_cache()
        
        return memory_id

    def find(self, err: Diagnostic, fix_question: str) -> List[Memory]:
        """
        Find exact or similar matches for a code example using Diagnostic information
        
        Args:
            err: Diagnostic object containing error information
            fix_question: The code to find matches for
            
        Returns:
            List of Memory objects representing the matches
        """
        # Default top_k value
        top_k = 3
        
        # Check for exact match first (using normalized code)
        normalized_code = normalize_code(fix_question)
        
        for memory in self.memories.values():
            if normalize_code(memory.faulty_code) == normalized_code:
                print(f"Found exact match: {memory.id}")
                return [memory]
        
        # If no exact match, use embeddings to find similar
        if not self.memories:
            print("No memories in database")
            return []
        
        # Generate embedding for query - include diagnostic information
        query_text = fix_question
        if hasattr(err, 'msg') and err.msg:
            query_text += f" {err.msg}"
        if hasattr(err, 'hint') and err.hint:
            query_text += f" {err.hint}"
        
        query_embedding = self.model.encode([query_text])[0]
        
        # Calculate similarities with all memory items
        similarities = []
        for memory_id, memory in self.memories.items():
            # Get or generate embedding for memory
            if not hasattr(memory, 'embedding') or memory.embedding is None:
                embedding_text = getattr(memory, 'embedding_text', memory.faulty_code)
                memory.embedding = self.model.encode([embedding_text])[0]
            
            # Calculate cosine similarity
            similarity = cosine_similarity([query_embedding], [memory.embedding])[0][0]
            similarities.append((memory_id, similarity))
        
        # Sort by similarity (descending) and return top k
        similarities.sort(key=lambda x: x[1], reverse=True)
        top_k_memories = [self.memories[memory_id] for memory_id, _ in similarities[:top_k]]
        
        return top_k_memories

    def add_from_example(self, example: CppBugExample) -> str:
        """Add a memory item from a CppBugExample"""
        # Create a simple Diagnostic object from the example
        err = Diagnostic(example.compiler_errors[0] if example.compiler_errors else "")
        if example.line_number:
            err.loc = example.line_number
        
        return self.add(
            err=err,
            fix_question=example.faulty_code,
            fix_answer=example.fixed_code
        )

    def create_sample_data(self, programs_path=None, output_path=None, output_yaml_path=None, create_embeddings=True):
        """
        Create sample memory data by reading buggy and fixed code files from programs directory.
        
        Args:
            programs_path: Path to the directory containing buggy/fixed code pairs.
                         If None, uses 'programs' directory in the same location as this file.
            output_path: Optional path for output JSON file. If not provided, 
                        will save to default location.
            output_yaml_path: Optional path for output YAML file.
            create_embeddings: Whether to create embeddings for semantic search
        
        Returns:
            Tuple of paths to the created JSON and YAML files.
        """
        # Define path to programs directory
        if programs_path is None:
            base_path = Path(__file__).parent
            programs_path = base_path / "programs"
        else:
            programs_path = Path(programs_path)
        
        # Verify programs directory exists
        if not programs_path.exists():
            print(f"Programs directory not found at {programs_path}")
            return None, None
        
        # Find all buggy/fixed file pairs
        code_pairs = []
        for buggy_file in programs_path.glob("*_buggy.*"):
            # Construct fixed file path with same extension
            fixed_file = buggy_file.parent / buggy_file.name.replace("_buggy", "_fixed")
            
            if fixed_file.exists():
                code_pairs.append((buggy_file, fixed_file))
        
        if not code_pairs:
            print("No buggy/fixed code pairs found")
            return None, None
        
        # Current timestamp
        current_time = datetime.now()
        timestamp = current_time.strftime("%Y%m%d%H%M")
        iso_timestamp = current_time.isoformat()
        
        # Create sample data with buggy and fixed code
        sample_data = []
        
        # Store text for embeddings
        embedding_texts = []
        
        for buggy_file, fixed_file in code_pairs:
            # Extract bug number from filename
            filename = buggy_file.name
            match = re.search(r'(\d+)_', filename)
            bug_number = match.group(1) if match else "0"
            
            # Detect language
            language = Memory.detect_language(buggy_file)
            language_code = Memory.get_language_code(language)
            
            # Read buggy and fixed code
            buggy_code = Memory.read_code_file(buggy_file)
            fixed_code = Memory.read_code_file(fixed_file)
            
            # Get compiler errors, analysis, and diagnostic
            compiler_errors, analysis, diagnostic = Memory.get_compiler_errors(buggy_code, language, filename)
            
            # Set file path in diagnostic
            diagnostic.file = str(buggy_file)
            
            # Generate bug description
            description = Memory.generate_bug_description(analysis, bug_number, filename)
            
            # Extract context for searching
            context = f"{language} programming bug fix: "
            if analysis.get('specific_issue'):
                context += analysis['specific_issue']
            else:
                # Use error type if specific issue not available
                context += analysis.get('error_type', 'code error').replace('_', ' ')
            
            # Store the embedding text
            embedding_text = analysis.get('embedding_text', f"{context} {buggy_code[:500]}")
            embedding_texts.append(embedding_text)
            
            # Create memory object using diagnostic and add to examples
            memory_id = self.add(
                err=diagnostic,
                fix_question=buggy_code,
                fix_answer=fixed_code
            )
            
            # Get the memory we just added and add to sample data
            memory = self.memories[memory_id]
            
            # Add to sample data for output
            memory_dict = {
                "id": memory_id,
                "content": memory.content,
                "keywords": memory.keywords,
                "context": memory.context,
                "tags": memory.tags,
                "timestamp": timestamp,
                "category": memory.category,
                "faulty_code": memory.faulty_code,
                "fixed_code": memory.fixed_code,
                "compiler_errors": compiler_errors,
                "language": memory.language,
                "created_at": iso_timestamp,
                "line_number": memory.line_number,
                "error_type": memory.error_type,
                "bug_category": memory.bug_category,
                "embedding_text": embedding_text,
                "embedding_index": -1  # Will be set after embedding creation
            }
            
            sample_data.append(memory_dict)
        
        # Create embeddings if requested
        if create_embeddings and embedding_texts:
            try:
                print(f"Creating embeddings for {len(embedding_texts)} code examples...")
                embeddings = self.model.encode(embedding_texts)
                print(f"Successfully created {len(embeddings)} embeddings")
                
                # Add embedding index to each memory and store embedding in memory object
                for i, (memory_dict, embedding) in enumerate(zip(sample_data, embeddings)):
                    memory_dict["embedding_index"] = i
                    memory_id = memory_dict["id"]
                    if memory_id in self.memories:
                        self.memories[memory_id].embedding = embedding
                
                # Determine embeddings output path - now in cached_memories directory with more descriptive name
                cache_dir = Path("cached_memories")
                cache_dir.mkdir(exist_ok=True)
                embeddings_path = cache_dir / "memory_embeddings.npy"
                
                # Save embeddings
                np.save(str(embeddings_path), embeddings)
                print(f"Saved embeddings to {embeddings_path}")
            except Exception as e:
                print(f"Error creating embeddings: {e}")
        
        # Determine output paths
        if output_path is None:
            # Use default path
            data_dir = Path(__file__).parent / "data"
            data_dir.mkdir(exist_ok=True)
            json_path = data_dir / "sample_memories.json"
        else:
            # Use provided path
            json_path = Path(output_path)
            json_path.parent.mkdir(exist_ok=True)
        
        if output_yaml_path is None:
            yaml_path = json_path.with_suffix('.yaml')
        else:
            yaml_path = Path(output_yaml_path)
            yaml_path.parent.mkdir(exist_ok=True)
        
        # Write to JSON file
        with open(json_path, "w") as f:
            json.dump(sample_data, f, indent=2)
        
        # Write to YAML file using ruamel.yaml
        yaml = YAML()
        yaml.indent(mapping=2, sequence=4, offset=2)  # Set indentation for better readability
        yaml.preserve_quotes = True  # Preserve quotes in strings
        
        with open(yaml_path, "w") as f:
            yaml.dump(sample_data, f)
        
        print(f"Created sample data at: {json_path} and {yaml_path}")
        print(f"Generated {len(sample_data)} memory entries from buggy/fixed code pairs")
        
        # Update database path and save the memory database
        self.db_path = str(yaml_path)
        self.save_database()
        
        return str(json_path), str(yaml_path)