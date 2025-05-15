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
        create_new_memories = True
        
        # Set the cache file path in the memory system
        memory_system.cache_file = str(memory_cache_file)
        
        if memory_cache_file.exists():
            print(f"Loading cached memories from {memory_cache_file}")
            try:
                with open(memory_cache_file, 'rb') as f:
                    memory_system.memories = pickle.load(f)
                print(f"Successfully loaded {len(memory_system.memories)} memories")
                create_new_memories = False
            except Exception as e:
                print(f"Error loading cached memories: {e}. Will recreate memories.")
        else:
            print(f"No cached memories found. Creating new memories.")
        
        if create_new_memories:
            # Load examples from the original database
            cpp_bug_examples = load_cpp_bugs_dataset(sample_db_path)
            print(f"Loaded {len(cpp_bug_examples)} examples from {sample_db_path}")
            
            # Add examples to our memory system
            print(f"Adding examples to memory system...")
            for example in cpp_bug_examples:
                memory_system.add_from_example(example)
                
            # Cache memories for future runs
            with open(memory_cache_file, 'wb') as f:
                pickle.dump(memory_system.memories, f)
            print(f"Successfully cached {len(memory_system.memories)} memories")
    
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
    def get_compiler_errors(code: str, language: str, file_name: str) -> Tuple[List[str], Dict[str, Any]]:
        """
        Compile the code and return errors and analysis.
        
        Args:
            code: The source code to compile
            language: The programming language
            file_name: Original file name for context
            
        Returns:
            Tuple of (error_messages, analysis_data)
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
        
        elif language == 'Verilog':
            # Placeholder for Verilog error analysis
            errors.append("Verilog compilation not implemented")
            analysis['description'] = "Verilog error analysis would be done here"
            
        elif language == 'VHDL':
            # Placeholder for VHDL error analysis
            errors.append("VHDL compilation not implemented")
            analysis['description'] = "VHDL error analysis would be done here"
            
        elif language == 'Chisel':
            # Placeholder for Chisel error analysis
            errors.append("Chisel compilation not implemented")
            analysis['description'] = "Chisel (Scala-based HDL) error analysis would be done here"
            
        elif language == 'PyRTL':
            # Placeholder for PyRTL error analysis
            errors.append("PyRTL compilation not implemented")
            analysis['description'] = "PyRTL error analysis would be done here"
            
        elif language == 'Spade':
            # Placeholder for Spade error analysis
            errors.append("Spade compilation not implemented")
            analysis['description'] = "Spade hardware description language error analysis would be done here"
            
        elif language == 'Silice':
            # Placeholder for Silice error analysis
            errors.append("Silice compilation not implemented")
            analysis['description'] = "Silice hardware description language error analysis would be done here"
        
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
        
        return errors, analysis

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
        
        # Check if database exists
        if not os.path.exists(self.db_path) and auto_create_data:
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
                # The database is now created and self.db_path is updated
        
        # Load the database (either existing or newly created)
        self.load_database()
    
    def load_database(self) -> None:
        """Load memories from database (JSON or YAML) if it exists"""
        if not os.path.exists(self.db_path):
            print(f"No existing database found at {self.db_path}")
            return
            
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
        except Exception as e:
            print(f"Error loading database: {e}")
            self.memories = {}
    
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
                memory.embedding = self.model.encode(embedding_text)
                
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
    
    def add(self, 
            original_code: str, 
            fixed_code: str = None, 
            errors: List[str] = None) -> str:
        """Add a new memory item"""
        # Determine error type from errors if possible
        error_type = "unknown"
        bug_category = "unknown"
        
        if errors and len(errors) > 0:
            # Try to extract error type from compiler errors
            first_error = errors[0].lower()
            if "syntax" in first_error:
                error_type = "syntax_error"
            elif "undefined" in first_error:
                error_type = "undefined_symbol"
            elif "redefinition" in first_error:
                error_type = "redefinition_error"
            elif "expected" in first_error:
                error_type = "missing_element"
            
            # Categorize the bug
            if any(kw in first_error for kw in ["memory", "allocation", "free", "leak"]):
                bug_category = "memory_management"
            elif any(kw in first_error for kw in ["type", "conversion"]):
                bug_category = "type_error"
            elif any(kw in first_error for kw in ["syntax", "token", "expected"]):
                bug_category = "syntax"
        
        # Generate a content description
        content = f"C++ Bug: Fix the {error_type if error_type != 'unknown' else 'bug'} in this code."
        
        if errors and len(errors) > 0:
            error_msg = errors[0].split('\n')[0] if '\n' in errors[0] else errors[0]
            content += f" Error: {error_msg}"
        
        # Create memory item
        memory_id = str(uuid.uuid4())
        memory_item = Memory(
            id=memory_id,
            content=content,
            keywords=["C++", error_type, "error", "bug"],
            context=f"C++ programming bug fix: {error_type}",
            tags=["debugging", error_type.replace('_', ' '), "cpp"],
            timestamp=datetime.now().strftime("%Y%m%d%H%M"),
            category="C++",
            faulty_code=original_code,
            fixed_code=fixed_code,
            compiler_errors=errors,
            language="cpp",
            error_type=error_type,
            bug_category=bug_category,
            embedding_text=f"C++ programming bug fix: {error_type} {original_code}"
        )
        
        # Add to memories and save
        self.memories[memory_id] = memory_item
        self.save_database()
        
        # Update the cache file if it exists
        if self.cache_file:
            try:
                with open(self.cache_file, 'wb') as f:
                    pickle.dump(self.memories, f)
            except Exception as e:
                print(f"Error updating cache file {self.cache_file}: {e}")
        
        return memory_id
    
    def find(self, original_code: str, errors: List[str] = None, program_path: Optional[Path] = None, save_results: bool = False) -> List[Memory]:
        """
        Find exact or similar matches for a code example
        
        Args:
            original_code: The code to find matches for
            errors: Optional list of compiler errors to aid in matching
            program_path: Optional path to the program file (for results saving)
            save_results: Whether to save results to a file
            
        Returns:
            List of Memory objects representing the matches
        """
        # Default top_k value
        top_k = 3
        
        # Check for exact match first (using normalized code)
        normalized_code = normalize_code(original_code)
        
        for memory in self.memories.values():
            if normalize_code(memory.faulty_code) == normalized_code:
                print(f"Found exact match: {memory.id}")
                matches = [memory]
                
                # Save results if requested and program_path is provided
                if save_results and program_path:
                    output_file = Memory.determine_output_file(None, program_path)
                    Memory.process_matches(matches, original_code, output_file)
                    
                return matches
        
        # If no exact match, use embeddings to find similar
        if not self.memories:
            print("No memories in database")
            return []
        
        # Generate embedding for query - if errors are provided, include them
        query_text = original_code
        if errors and len(errors) > 0:
            error_summary = " ".join(errors[:3])  # Include up to 3 errors in the embedding
            query_text = f"{original_code} {error_summary}"
        
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
        
        # Save results if requested and program_path is provided
        if save_results and program_path:
            output_file = Memory.determine_output_file(None, program_path)
            Memory.process_matches(top_k_memories, original_code, output_file)
        
        return top_k_memories
    
    def add_from_example(self, example: CppBugExample) -> str:
        """Add a memory item from a CppBugExample"""
        return self.add(
            original_code=example.faulty_code,
            fixed_code=example.fixed_code,
            errors=example.compiler_errors
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
            
            # Get compiler errors and analysis
            compiler_errors, analysis = Memory.get_compiler_errors(buggy_code, language, filename)
            
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
            
            # Create memory object
            memory_id = str(uuid.uuid4())
            
            # Determine bug category, prioritizing analysis results over filename patterns
            bug_category = "unknown"
            if analysis.get('bug_category') and analysis['bug_category'] != "unknown":
                bug_category = analysis['bug_category']
            elif analysis.get('error_type') and analysis['error_type'] != "unknown":
                # Use error type as category if specific category not available
                bug_category = analysis['error_type'].replace('_', ' ')
            else:
                # As last resort, try to extract from filename pattern
                bug_category = Memory.extract_bug_type(filename)
            
            memory = Memory(
                id=memory_id,
                content=f"{language} Bug #{bug_number}: {description}",
                keywords=analysis['keywords'],
                context=context,
                tags=analysis['tags'],
                timestamp=timestamp,
                category=language,
                faulty_code=buggy_code,
                fixed_code=fixed_code,
                compiler_errors=compiler_errors,
                language=language_code,
                line_number=analysis.get('line_number'),
                error_type=analysis.get('error_type', 'unknown'),
                bug_category=bug_category,
                embedding_text=embedding_text
            )
            
            # Add to memories dictionary
            self.memories[memory_id] = memory
            
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
                "compiler_errors": memory.compiler_errors,
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