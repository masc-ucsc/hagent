import json
import os
from typing import List, Dict, Optional, Union
from datetime import datetime
from sentence_transformers import SentenceTransformer
from sklearn.metrics.pairwise import cosine_similarity
import numpy as np
import uuid
from pathlib import Path
from ruamel.yaml import YAML

from utils import normalize_code, CppBugExample

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

class FewShotMemory:
    """Simple memory system with embedding-based retrieval for C++ code bug examples"""
    
    def __init__(self, 
                 db_path: str = "data/sample_memories.yaml", 
                 model_name: str = "all-MiniLM-L6-v2"):
        """Initialize the memory system"""
        self.db_path = db_path
        self.model = SentenceTransformer(model_name)
        self.memories = {}  # Stores Memory objects by ID
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
            
            print(f"Saved {len(self.memories)} items to database at {output_path}")
        except Exception as e:
            print(f"Error saving database to {output_path}: {e}")
    
    def add(self, 
            faulty_code: str, 
            fixed_code: str = None, 
            error_type: str = "unknown", 
            bug_category: str = "unknown",
            compiler_errors: List[str] = None,
            content: str = None) -> str:
        """Add a new memory item"""
        # Generate a content description if not provided
        if content is None:
            content = f"C++ Bug: Fix the {error_type if error_type != 'unknown' else 'bug'} in this code."
            
            if compiler_errors and len(compiler_errors) > 0:
                error_msg = compiler_errors[0].split('\n')[0] if '\n' in compiler_errors[0] else compiler_errors[0]
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
            faulty_code=faulty_code,
            fixed_code=fixed_code,
            compiler_errors=compiler_errors,
            language="cpp",
            error_type=error_type,
            bug_category=bug_category,
            embedding_text=f"C++ programming bug fix: {error_type} {faulty_code}"
        )
        
        # Add to memories and save
        self.memories[memory_id] = memory_item
        self.save_database()
        
        return memory_id
    
    def find(self, code: str, top_k: int = 3) -> List[Memory]:
        """Find exact or similar matches for a code example"""
        # Check for exact match first (using normalized code)
        normalized_code = normalize_code(code)
        
        for memory in self.memories.values():
            if normalize_code(memory.faulty_code) == normalized_code:
                print(f"Found exact match: {memory.id}")
                return [memory]
        
        # If no exact match, use embeddings to find similar
        if not self.memories:
            print("No memories in database")
            return []
        
        # Generate embedding for query
        query_embedding = self.model.encode([code])[0]
        
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
            faulty_code=example.faulty_code,
            fixed_code=example.fixed_code,
            error_type=example.error_type,
            bug_category=example.bug_category,
            compiler_errors=example.compiler_errors,
            content=example.content
        )