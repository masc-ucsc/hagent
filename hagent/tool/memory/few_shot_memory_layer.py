# hagent/tool/memory/few_shot_memory_layer.py

# Set tokenizers parallelism to false to avoid warnings with forked processes
import os
os.environ["TOKENIZERS_PARALLELISM"] = "false"

import json
import os
import uuid
import pickle
import numpy as np
from typing import List, Dict, Optional, Any, Tuple
from datetime import datetime
from sentence_transformers import SentenceTransformer
from sklearn.metrics.pairwise import cosine_similarity
from pathlib import Path
from ruamel.yaml import YAML

from hagent.tool.memory.utils import normalize_code
from hagent.tool.compile import Diagnostic

class MemoryItem:
    """Memory item for storing code fixes with confidence score"""
    def __init__(self, 
                 error_type: str,
                 fix_question: str, 
                 fix_answer: str,
                 confidence: float = 1.0,
                 id: Optional[str] = None,
                 timestamp: Optional[str] = None):
        self.id = id or str(uuid.uuid4())
        self.error_type = error_type
        self.fix_question = fix_question
        self.fix_answer = fix_answer
        self.confidence = confidence
        self.timestamp = timestamp or datetime.now().strftime("%Y%m%d%H%M")
        self._embedding = None  # Embedding is stored separately in the embeddings file
    
    @property
    def embedding(self):
        """Get the embedding - this is accessed via the parent Memory object"""
        return self._embedding
    
    @embedding.setter
    def embedding(self, value):
        """Set the embedding - this is managed via the parent Memory object"""
        self._embedding = value
    
    def to_dict(self) -> Dict[str, Any]:
        """Convert memory item to dictionary for serialization"""
        # Include embeddings in the dictionary for YAML storage
        return {
            "id": self.id,
            "error_type": self.error_type,
            "fix_question": self.fix_question,
            "fix_answer": self.fix_answer,
            "confidence": self.confidence,
            "timestamp": self.timestamp,
            "embedding": self._embedding.tolist() if self._embedding is not None else None
        }
    
    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> 'MemoryItem':
        """Create memory item from dictionary"""
        item = cls(
            error_type=data["error_type"],
            fix_question=data["fix_question"],
            fix_answer=data["fix_answer"],
            confidence=data.get("confidence", 1.0),
            id=data.get("id"),
            timestamp=data.get("timestamp")
        )
        
        # Handle embedding data if present in the dictionary
        if "embedding" in data and data["embedding"] is not None:
            try:
                item._embedding = np.array(data["embedding"])
            except Exception as e:
                print(f"Warning: Could not convert embedding from dict: {e}")
                
        return item

class Memory:
    """Core memory system with add and find methods using Diagnostic objects"""
    
    def __init__(self, 
                 db_path: Optional[str] = None, 
                 model_name: str = "all-MiniLM-L6-v2"):
        """Initialize the memory system
        
        Args:
            db_path: Path to the database file
            model_name: Name of the sentence transformer model
        """
        # Initialize the model for embeddings
        self.model = SentenceTransformer(model_name)
        self.memories: Dict[str, MemoryItem] = {}
        self.embeddings: Dict[str, np.ndarray] = {}
        
        # Set up database path with descriptive names
        data_dir = Path("data")
        data_dir.mkdir(exist_ok=True)
        
        if db_path:
            self.db_path = str(db_path)
        else:
            # More descriptive default file name
            self.db_path = str(data_dir / "code_fix_memory_database.yaml")
        
        # Compute embeddings path - use the same base name but with a descriptive suffix
        db_path_obj = Path(self.db_path)
        self.embeddings_path = str(db_path_obj.with_stem(f"{db_path_obj.stem}_embeddings")) + ".pkl"
        
        # Load database and embeddings if they exist
        if os.path.exists(self.db_path):
            self.load_database()
        if os.path.exists(self.embeddings_path):
            self.load_embeddings()
            
        # Sync embeddings between memory items and the embeddings dictionary
        self._sync_embeddings()
    
    def _sync_embeddings(self):
        """Synchronize embeddings between YAML data and pickle file"""
        # Check for embeddings in memory items that aren't in the embeddings dictionary
        for memory_id, memory_item in self.memories.items():
            if memory_item.embedding is not None and memory_id not in self.embeddings:
                self.embeddings[memory_id] = memory_item.embedding
                
        # Check for embeddings in the dictionary that aren't attached to memory items
        for memory_id, embedding in self.embeddings.items():
            if memory_id in self.memories:
                self.memories[memory_id].embedding = embedding
    
    def add(self, err: Diagnostic, fix_question: str, fix_answer: str) -> None:
        """Add a new memory item using a Diagnostic object
        
        Args:
            err: Diagnostic object containing error information
            fix_question: Original code with the error
            fix_answer: Fixed code
        """
        # Extract error type from diagnostic
        error_type = err.msg
        
        # Check if a similar item already exists
        for item in self.memories.values():
            if (item.error_type == error_type and 
                normalize_code(item.fix_question) == normalize_code(fix_question)):
                print(f"Skipping duplicate entry for error type: {error_type}")
                return
        
        # Create a new memory item
        memory_item = MemoryItem(
            error_type=error_type,
            fix_question=fix_question,
            fix_answer=fix_answer
        )
        
        # Generate embedding for the item
        item_text = f"{error_type} {fix_question}"
        embedding = self.model.encode(item_text)
        
        # Store embedding in both places
        self.embeddings[memory_item.id] = embedding
        memory_item.embedding = embedding
        
        # Add item to memory
        self.memories[memory_item.id] = memory_item
        
        # Save database and embeddings
        self.save_database()
        self.save_embeddings()
        
        print(f"Added new memory item with ID '{memory_item.id}' for error type: '{error_type}'")
    
    def find(self, err: Diagnostic, fix_question: str) -> List[MemoryItem]:
        """Find memory items that match the given error and code
        
        Args:
            err: Diagnostic object containing error information
            fix_question: Code to find similar examples for
            
        Returns:
            List of memory items sorted by relevance
        """
        error_type = err.msg
        normalized_question = normalize_code(fix_question)
        
        # First check for exact matches based on error type and normalized code
        exact_matches = []
        for item in self.memories.values():
            if (item.error_type == error_type and 
                normalize_code(item.fix_question) == normalized_question):
                # Set highest confidence for exact matches
                item.confidence = 1.0
                # Add the embedding for convenience
                if item.embedding is None and item.id in self.embeddings:
                    item.embedding = self.embeddings[item.id]
                exact_matches.append(item)
        
        if exact_matches:
            return exact_matches
        
        # If no exact matches, use semantic similarity
        if not self.memories:
            return []
        
        # Create combined text for embedding
        query_text = f"{error_type} {fix_question}"
        query_embedding = self.model.encode(query_text)
        
        # Calculate similarity scores
        results = []
        for memory_id, item in self.memories.items():
            # Check for embedding in the item first, then in the dictionary
            embedding = None
            if item.embedding is not None:
                embedding = item.embedding
            elif memory_id in self.embeddings:
                embedding = self.embeddings[memory_id]
                item.embedding = embedding  # Update item's embedding
            
            # Generate missing embeddings
            if embedding is None:
                item_text = f"{item.error_type} {item.fix_question}"
                embedding = self.model.encode(item_text)
                # Store in both places
                self.embeddings[memory_id] = embedding
                item.embedding = embedding
                self.save_embeddings()
                self.save_database()  # Also update the YAML file with the new embedding
            
            # Calculate similarity
            similarity = cosine_similarity([query_embedding], [embedding])[0][0]
            
            # Set confidence based on similarity
            item.confidence = float(similarity)
            
            # Only add items with reasonable similarity
            if similarity > 0.5:
                results.append(item)
        
        # Sort by confidence (descending)
        results.sort(key=lambda x: x.confidence, reverse=True)
        
        # Return top 3 results or all if fewer
        return results[:3]
    
    def load_database(self) -> None:
        """Load memories from database file (including embeddings if present)"""
        try:
            path = Path(self.db_path)
            suffix = path.suffix.lower()
            
            if suffix == '.json':
                with open(self.db_path, 'r') as f:
                    data = json.load(f)
            elif suffix in ['.yaml', '.yml']:
                yaml = YAML(typ='safe')
                with open(self.db_path, 'r') as f:
                    data = yaml.load(f)
                    if data is None:
                        data = []
            else:
                print(f"Unsupported file format: {suffix}")
                return
            
            # Convert data to Memory objects
            for item_data in data:
                try:
                    memory_item = MemoryItem.from_dict(item_data)
                    self.memories[memory_item.id] = memory_item
                    
                    # If the item has an embedding, also add it to the embeddings dictionary
                    if memory_item.embedding is not None:
                        self.embeddings[memory_item.id] = memory_item.embedding
                except Exception as e:
                    print(f"Warning: Could not load memory item: {e}. Skipping.")
            
            print(f"Loaded {len(self.memories)} items from database at {self.db_path}")
        except Exception as e:
            print(f"Error loading database: {e}")
    
    def save_database(self) -> None:
        """Save memories to database file (including embeddings)"""
        try:
            path = Path(self.db_path)
            path.parent.mkdir(exist_ok=True)
            
            # First, try to load any existing data to make sure we don't overwrite it
            existing_data = {}
            if os.path.exists(self.db_path):
                try:
                    suffix = path.suffix.lower()
                    if suffix == '.json':
                        with open(self.db_path, 'r') as f:
                            existing_data_list = json.load(f)
                            # Convert list to dictionary by ID
                            for item in existing_data_list:
                                if 'id' in item:
                                    existing_data[item['id']] = item
                    elif suffix in ['.yaml', '.yml']:
                        yaml = YAML(typ='safe')
                        with open(self.db_path, 'r') as f:
                            existing_data_list = yaml.load(f) or []
                            # Convert list to dictionary by ID
                            for item in existing_data_list:
                                if 'id' in item:
                                    existing_data[item['id']] = item
                except Exception as e:
                    print(f"Warning: Couldn't read existing database, creating new file: {e}")
            
            # Update memory items with embeddings from the dictionary if needed
            for memory_id, memory in self.memories.items():
                if memory.embedding is None and memory_id in self.embeddings:
                    memory.embedding = self.embeddings[memory_id]
            
            # Merge existing data with current memories, prioritizing current memories
            merged_data = {**existing_data}
            for memory_id, memory in self.memories.items():
                merged_data[memory_id] = memory.to_dict()
            
            # Convert back to list for saving
            memory_list = list(merged_data.values())
            
            # Save based on file extension
            suffix = path.suffix.lower()
            
            if suffix == '.json':
                # Create temp file to avoid partial writes
                temp_path = f"{self.db_path}.tmp"
                with open(temp_path, 'w') as f:
                    json.dump(memory_list, f, indent=2)
                # Rename temp file to target file (atomic operation)
                os.replace(temp_path, self.db_path)
            elif suffix in ['.yaml', '.yml']:
                yaml = YAML()
                yaml.indent(mapping=2, sequence=4, offset=2)
                # Create temp file to avoid partial writes
                temp_path = f"{self.db_path}.tmp"
                with open(temp_path, 'w') as f:
                    yaml.dump(memory_list, f)
                # Rename temp file to target file (atomic operation)
                os.replace(temp_path, self.db_path)
            else:
                # Default to JSON if extension not recognized
                temp_path = f"{self.db_path}.json.tmp"
                with open(temp_path, 'w') as f:
                    json.dump(memory_list, f, indent=2)
                # Rename temp file to target file (atomic operation)
                os.replace(temp_path, f"{self.db_path}.json")
                
            print(f"Saved {len(memory_list)} items to database at {self.db_path}")
        except Exception as e:
            print(f"Error saving database: {e}")
    
    def load_embeddings(self) -> None:
        """Load embeddings from pickle file"""
        try:
            if os.path.exists(self.embeddings_path):
                with open(self.embeddings_path, 'rb') as f:
                    self.embeddings = pickle.load(f)
                print(f"Loaded {len(self.embeddings)} embeddings from {self.embeddings_path}")
                
                # Check for missing embeddings for existing memories
                missing_embeddings = set(self.memories.keys()) - set(self.embeddings.keys())
                if missing_embeddings:
                    print(f"Generating {len(missing_embeddings)} missing embeddings...")
                    self._generate_missing_embeddings(missing_embeddings)
            else:
                print(f"No embeddings file found at {self.embeddings_path}")
                # Initialize embeddings for all memories
                if self.memories:
                    print(f"Generating embeddings for {len(self.memories)} memories...")
                    self._generate_missing_embeddings(self.memories.keys())
        except Exception as e:
            print(f"Error loading embeddings: {e}")
            self.embeddings = {}
    
    def save_embeddings(self) -> None:
        """Save embeddings to pickle file"""
        try:
            # Create directory if it doesn't exist
            embeddings_dir = Path(self.embeddings_path).parent
            embeddings_dir.mkdir(exist_ok=True)
            
            # Create temp file to avoid partial writes
            temp_path = f"{self.embeddings_path}.tmp"
            with open(temp_path, 'wb') as f:
                pickle.dump(self.embeddings, f)
            
            # Rename temp file to target file (atomic operation)
            os.replace(temp_path, self.embeddings_path)
            
            print(f"Saved {len(self.embeddings)} embeddings to {self.embeddings_path}")
        except Exception as e:
            print(f"Error saving embeddings: {e}")
    
    def _generate_missing_embeddings(self, memory_ids: List[str]) -> None:
        """Generate embeddings for the given memory IDs"""
        for memory_id in memory_ids:
            if memory_id in self.memories:
                memory = self.memories[memory_id]
                item_text = f"{memory.error_type} {memory.fix_question}"
                embedding = self.model.encode(item_text)
                
                # Store embedding in both places
                self.embeddings[memory_id] = embedding
                memory.embedding = embedding
        
        # Save the updated embeddings to both files
        self.save_embeddings()
        self.save_database()
    
    # Helper method for reading code files (useful for testing)
    @staticmethod
    def read_code_file(file_path):
        """Read code from a file"""
        try:
            with open(file_path, 'r') as f:
                return f.read()
        except Exception as e:
            print(f"Error reading file {file_path}: {e}")
            return None

# For backward compatibility
FewShotMemory = Memory