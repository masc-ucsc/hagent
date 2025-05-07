import json
import os
import pickle
import sys
from typing import List, Dict, Optional, Union, Tuple
from datetime import datetime
from sentence_transformers import SentenceTransformer
from sklearn.metrics.pairwise import cosine_similarity
import numpy as np
import uuid
from pathlib import Path
from ruamel.yaml import YAML

from utils import normalize_code, CppBugExample, load_cpp_bugs_dataset

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
                       output_file: str) -> None:
        """Process and display matches found by the memory system"""
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
            Memory.save_examples_to_yaml(matches, test_code, output_file, exact_match)
        else:
            print("No similar examples found")
            Memory.save_examples_to_yaml([], test_code, output_file, False)
    
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
        """Determine the output file path"""
        if not output_file:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            file_name = program_path.stem
            output_file = f"results/{file_name}_matches_{timestamp}.yaml"
        return output_file

class FewShotMemory:
    """Simple memory system with embedding-based retrieval for C++ code bug examples"""
    
    def __init__(self, 
                 db_path: str = "data/sample_memories.yaml", 
                 model_name: str = "all-MiniLM-L6-v2",
                 cache_file: str = None):
        """Initialize the memory system"""
        self.db_path = db_path
        self.model = SentenceTransformer(model_name)
        self.memories = {}  # Stores Memory objects by ID
        self.cache_file = cache_file
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
    
    def find(self, original_code: str, errors: List[str] = None) -> List[Memory]:
        """Find exact or similar matches for a code example"""
        # Default top_k value
        top_k = 3
        
        # Check for exact match first (using normalized code)
        normalized_code = normalize_code(original_code)
        
        for memory in self.memories.values():
            if normalize_code(memory.faulty_code) == normalized_code:
                print(f"Found exact match: {memory.id}")
                return [memory]
        
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
        
        return top_k_memories
    
    def add_from_example(self, example: CppBugExample) -> str:
        """Add a memory item from a CppBugExample"""
        return self.add(
            original_code=example.faulty_code,
            fixed_code=example.fixed_code,
            errors=example.compiler_errors
        )