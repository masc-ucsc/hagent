"""
FewShotMemory module for hagent - provides a semantic memory layer for LLM agents.
"""

import os
import json
import uuid
import time
import datetime
import numpy as np
import pickle
from pathlib import Path
from typing import List, Dict, Optional, Any, Union, Tuple
from sentence_transformers import SentenceTransformer
from sklearn.metrics.pairwise import cosine_similarity

from hagent.core.llm_template import LLM_template
from hagent.core.llm_wrap import LLM_wrap
from hagent.core.step import Step
from hagent.tool.memory.db_memory_store import SQLiteMemoryStore

class Memory:
    """Memory unit with structured metadata"""
    def __init__(self, 
                 content: str,
                 id: Optional[str] = None,
                 keywords: Optional[List[str]] = None,
                 links: Optional[List[str]] = None,
                 importance_score: Optional[float] = None,
                 retrieval_count: Optional[int] = None,
                 timestamp: Optional[str] = None,
                 last_accessed: Optional[str] = None,
                 context: Optional[str] = None, 
                 evolution_history: Optional[List] = None,
                 category: Optional[str] = None,
                 tags: Optional[List[str]] = None,
                 faulty_code: Optional[str] = None,
                 fixed_code: Optional[str] = None,
                 compiler_errors: Optional[List[str]] = None,
                 language: Optional[str] = None,
                 llm_interface: Optional[LLM_wrap] = None):
        
        self.content = content
        
        # Generate metadata using LLM if not provided and LLM interface is available
        if llm_interface and any(param is None for param in [keywords, context, category, tags]):
            if faulty_code:
                # If we have code, use code analysis
                analysis = self.analyze_code(faulty_code, language, llm_interface)
                keywords = keywords or analysis.get("keywords", [])
                context = context or "Code debugging"
                tags = tags or [language] if language else []
            else:
                # Otherwise use content analysis
                analysis = self.analyze_content(content, llm_interface)
                keywords = keywords or analysis.get("keywords", [])
                context = context or analysis.get("context", "General")
                tags = tags or analysis.get("tags", [])
        
        # Set default values for optional parameters
        self.id = id or str(uuid.uuid4())
        self.keywords = keywords or []
        self.links = links or []
        self.importance_score = importance_score or 1.0
        self.retrieval_count = retrieval_count or 0
        current_time = datetime.datetime.now().strftime("%Y%m%d%H%M")
        self.timestamp = timestamp or current_time
        self.last_accessed = last_accessed or current_time
        
        # Handle context that can be either string or list
        self.context = context or "General"
        if isinstance(self.context, list):
            self.context = " ".join(self.context)  # Convert list to string by joining
            
        self.evolution_history = evolution_history or []
        self.category = category or "Uncategorized"
        self.tags = tags or []

        # Code-specific fields
        self.faulty_code = faulty_code or ""
        self.fixed_code = fixed_code or ""
        self.compiler_errors = compiler_errors or []
        self.language = language or ""

    @staticmethod
    def analyze_content(content: str, llm_interface: LLM_wrap) -> Dict:
        """Analyze content to extract keywords, context, and other metadata"""
        prompt_data = {"content": content}
        
        # Try to use a template named 'memory_analysis' from the LLM config
        try:
            results = llm_interface.inference(prompt_data, 'memory_analysis', n=1)
            if results and len(results) > 0:
                try:
                    return json.loads(results[0])
                except json.JSONDecodeError:
                    # If not JSON, create a simple structure
                    print(f"Warning: Memory analysis returned non-JSON: {results[0]}")
                    words = [w for w in content.split() if len(w) > 3]
                    return {
                        "keywords": words[:min(5, len(words))],
                        "context": content[:100],
                        "tags": []
                    }
            
        except Exception as e:
            print(f"Error analyzing content: {str(e)}")
        
        # Fallback if the template doesn't exist or other errors
        words = [w for w in content.split() if len(w) > 3]
        return {
            "keywords": words[:min(5, len(words))],
            "context": content[:100],
            "tags": []
        }

    @staticmethod
    def analyze_code(code: str, language: str, llm_interface: LLM_wrap) -> Dict:
        """Analyze code to extract keywords, bugs, and other metadata"""
        prompt_data = {
            "faulty_code": code,
            "language": language or "unknown"
        }
        
        # Try to use a template named 'code_analysis' from the LLM config
        try:
            results = llm_interface.inference(prompt_data, 'code_analysis', n=1)
            if results and len(results) > 0:
                try:
                    return json.loads(results[0])
                except json.JSONDecodeError:
                    # If not JSON, create a simple structure
                    print(f"Warning: Code analysis returned non-JSON: {results[0]}")
                    return {
                        "keywords": [language] if language else [],
                        "bugs": ["Unknown issues"],
                        "severity": "unknown"
                    }
            
        except Exception as e:
            print(f"Error analyzing code: {str(e)}")
        
        # Fallback if the template doesn't exist or other errors
        return {
            "keywords": [language] if language else [],
            "bugs": ["Unknown issues"],
            "severity": "unknown"
        }

    @staticmethod
    def fix_code(code: str, compiler_errors: List[str], language: str, llm_interface: LLM_wrap) -> str:
        """Generate a fixed version of the code using LLM"""
        prompt_data = {
            "faulty_code": code,
            "compiler_errors": compiler_errors,
            "language": language or "unknown"
        }
        
        # Try to use a template named 'code_fix' from the LLM config
        try:
            results = llm_interface.inference(prompt_data, 'code_fix', n=1)
            if results and len(results) > 0:
                return results[0]
            
        except Exception as e:
            print(f"Error fixing code: {str(e)}")
        
        # Fallback if error or no results
        return code

    def to_dict(self) -> Dict:
        """Serialize the Memory to a dictionary"""
        return {
            "id": self.id,
            "content": self.content,
            "keywords": self.keywords,
            "links": self.links,
            "importance_score": self.importance_score,
            "retrieval_count": self.retrieval_count,
            "timestamp": self.timestamp,
            "last_accessed": self.last_accessed,
            "context": self.context,
            "evolution_history": self.evolution_history,
            "category": self.category,
            "tags": self.tags,
            "faulty_code": self.faulty_code,
            "fixed_code": self.fixed_code,
            "compiler_errors": self.compiler_errors,
            "language": self.language
        }
    
    @classmethod
    def from_dict(cls, data: Dict) -> 'Memory':
        """Create a Memory from a dictionary"""
        return cls(
            content=data["content"],
            id=data.get("id"),
            keywords=data.get("keywords"),
            links=data.get("links"),
            importance_score=data.get("importance_score"),
            retrieval_count=data.get("retrieval_count"),
            timestamp=data.get("timestamp"),
            last_accessed=data.get("last_accessed"),
            context=data.get("context"),
            evolution_history=data.get("evolution_history"),
            category=data.get("category"),
            tags=data.get("tags"),
            faulty_code=data.get("faulty_code"),
            fixed_code=data.get("fixed_code"),
            compiler_errors=data.get("compiler_errors"),
            language=data.get("language")
        )


class EmbeddingRetriever:
    """Semantic retrieval system using text embeddings"""
    
    def __init__(self, model_name: str = 'all-MiniLM-L6-v2'):
        """Initialize the retriever with a sentence transformer model"""
        self.model = SentenceTransformer(model_name)
        self.corpus = []  # Original text items
        self.embeddings = None  # Numpy array of embeddings
        self.document_map = {}  # Maps document content to its index
    
    def add_documents(self, documents: List[str]) -> None:
        """Add multiple documents to the retriever"""
        if not documents:
            return
            
        # Track current size to know where to add new documents
        start_idx = len(self.corpus)
        
        # Add to corpus
        self.corpus.extend(documents)
        
        # Update document map
        for idx, doc in enumerate(documents, start=start_idx):
            self.document_map[doc] = idx
        
        # Generate embeddings for new documents
        new_embeddings = self.model.encode(documents)
        
        # Update embeddings array
        if self.embeddings is None:
            self.embeddings = new_embeddings
        else:
            self.embeddings = np.vstack([self.embeddings, new_embeddings])
    
    def search(self, query: str, k: int = 5) -> List[int]:
        """Search for documents similar to the query"""
        if not self.corpus or len(self.corpus) == 0:
            return []
        
        # Encode query
        query_embedding = self.model.encode([query])[0]
        
        # Calculate cosine similarities
        similarities = cosine_similarity([query_embedding], self.embeddings)[0]
        
        # Get top-k indices
        k = min(k, len(self.corpus))
        top_k_indices = np.argsort(similarities)[-k:][::-1]
        
        return top_k_indices.tolist()
    
    def save(self, retriever_file: str, embeddings_file: str) -> None:
        """Save retriever state to disk"""
        # Save embeddings using numpy
        if self.embeddings is not None:
            np.save(embeddings_file, self.embeddings)
        
        # Save other attributes
        state = {
            'corpus': self.corpus,
            'document_map': self.document_map,
            'model_name': self.model.__class__.__name__
        }
        with open(retriever_file, 'wb') as f:
            pickle.dump(state, f)
    
    @classmethod
    def load(cls, retriever_file: str, embeddings_file: str) -> 'EmbeddingRetriever':
        """Load retriever state from disk"""
        retriever = cls()
        
        # Load embeddings
        if os.path.exists(embeddings_file):
            retriever.embeddings = np.load(embeddings_file)
        
        # Load other attributes
        if os.path.exists(retriever_file):
            with open(retriever_file, 'rb') as f:
                state = pickle.load(f)
                retriever.corpus = state.get('corpus', [])
                retriever.document_map = state.get('document_map', {})
        
        return retriever


class FewShotMemory(Step):
    """Memory management system with semantic retrieval for hagent"""
    
    def __init__(self, 
                name: str = "few_shot_memory",
                conf_file: str = None, 
                log_file: str = None,
                model_name: str = 'all-MiniLM-L6-v2',
                llm_backend: str = "openai",
                llm_model: str = "gpt-4",
                memory_dir: str = None,
                use_sqlite: bool = False,
                db_path: str = None):
        """Initialize the FewShotMemory system"""
        super().__init__()
        
        # Set default memory directory
        if memory_dir is None:
            memory_dir = os.path.join(os.path.dirname(__file__), "memories")
        os.makedirs(memory_dir, exist_ok=True)
        self.memory_dir = memory_dir
        
        # Set up retriever
        self.retriever = EmbeddingRetriever(model_name)
        
        # Set up LLM for metadata generation
        if conf_file:
            self.llm = LLM_wrap(
                name=name,
                conf_file=conf_file,
                log_file=log_file or f"{name}_memory.log"
            )
        else:
            # Create a default LLM configuration if none provided
            self.llm = None
        
        # Storage for memory notes
        self.memories = {}
        
        # Use SQLite for storage if specified
        self.use_sqlite = use_sqlite
        if use_sqlite:
            if db_path is None:
                db_path = os.path.join(memory_dir, f"{name}_memories.db")
            self.db_store = SQLiteMemoryStore(db_path)
        else:
            self.db_store = None
        
        # Metadata
        self.total_memories = 0
        self.last_error = None
        
        # Set file paths for persistence
        self.memory_file = os.path.join(memory_dir, f"{name}_memories.pkl")
        self.retriever_file = os.path.join(memory_dir, f"{name}_retriever.pkl")
        self.embeddings_file = os.path.join(memory_dir, f"{name}_embeddings.npy")
        
        # Load existing memories if available
        self._load_memories()
    
    def _load_memories(self) -> None:
        """Load memories from disk or database if available"""
        if self.use_sqlite and self.db_store:
            # Load from SQLite
            try:
                memory_dicts = self.db_store.get_all_memories()
                self.memories = {m["id"]: Memory.from_dict(m) for m in memory_dicts}
                self.total_memories = len(self.memories)
                
                # Rebuild retriever from memories
                self._rebuild_retriever()
            except Exception as e:
                self.last_error = f"Error loading memories from database: {str(e)}"
                self.memories = {}
        else:
            # Load from file
            if os.path.exists(self.memory_file):
                try:
                    with open(self.memory_file, 'rb') as f:
                        self.memories = pickle.load(f)
                    self.total_memories = len(self.memories)
                    
                    # Load retriever if available
                    if os.path.exists(self.retriever_file) and os.path.exists(self.embeddings_file):
                        self.retriever = EmbeddingRetriever.load(self.retriever_file, self.embeddings_file)
                    else:
                        # Rebuild retriever from memories
                        self._rebuild_retriever()
                except Exception as e:
                    self.last_error = f"Error loading memories from file: {str(e)}"
                    self.memories = {}
    
    def _save_memories(self) -> None:
        """Save memories to disk or database"""
        try:
            if self.use_sqlite and self.db_store:
                # We don't need to save to database here, as we update it in real-time
                # with add_memory and delete_memory operations
                pass
            else:
                # Save to file
                with open(self.memory_file, 'wb') as f:
                    pickle.dump(self.memories, f)
            
            # Save retriever state
            self.retriever.save(self.retriever_file, self.embeddings_file)
        except Exception as e:
            self.last_error = f"Error saving memories: {str(e)}"
    
    def _rebuild_retriever(self) -> None:
        """Rebuild retriever from memories"""
        # Extract content and metadata from memories
        documents = []
        for memory in self.memories.values():
            # Combine memory content, metadata, and code for better retrieval
            metadata = f" {memory.context} {' '.join(memory.keywords)} {' '.join(memory.tags)}"
            code_content = ""
            if memory.faulty_code:
                code_content = f" {memory.faulty_code}"
            documents.append(memory.content + metadata + code_content)
        
        # Reset and rebuild retriever
        self.retriever = EmbeddingRetriever()
        self.retriever.add_documents(documents)
    
    def add_memory(self, content: str, **kwargs) -> str:
        """
        Add a new memory note to the system
        
        Args:
            content: The main content of the memory
            **kwargs: Additional metadata for the memory
            
        Returns:
            The ID of the new memory note
        """
        # Create a memory note
        note = Memory(content=content, llm_interface=self.llm, **kwargs)
        
        # Store the note
        self.memories[note.id] = note
        self.total_memories += 1
        
        # If using SQLite, also add to database
        if self.use_sqlite and self.db_store:
            self.db_store.add_memory(note.to_dict())
        
        # Update retriever
        metadata = f" {note.context} {' '.join(note.keywords)} {' '.join(note.tags)}"
        self.retriever.add_documents([note.content + metadata])
        
        # Save to disk
        self._save_memories()
        
        return note.id
    
    def delete_memory(self, memory_id: str) -> bool:
        """
        Delete a memory from the system.
        
        Args:
            memory_id: ID of the memory to delete
            
        Returns:
            True if successful, False if memory not found
        """
        # Check if memory exists
        if memory_id not in self.memories:
            return False
        
        # Remove from internal dictionary
        del self.memories[memory_id]
        self.total_memories -= 1
        
        # If using SQLite, also delete from database
        if self.use_sqlite and self.db_store:
            self.db_store.delete_memory(memory_id)
        
        # We need to rebuild the retriever since memory contents have changed
        self._rebuild_retriever()
        
        # Save to disk
        self._save_memories()
        
        return True
    
    def retrieve_memories(self, query: str, k: int = 5) -> List[Memory]:
        """
        Retrieve memories relevant to the query
        
        Args:
            query: The search query
            k: Number of memories to retrieve
            
        Returns:
            List of Memory objects
        """
        if not self.memories:
            return []
        
        # Get indices of relevant memories
        indices = self.retriever.search(query, k)
        
        # Convert to list of memories
        memories_list = list(self.memories.values())
        retrieved_memories = [memories_list[i] for i in indices]
        
        # Update retrieval counts
        for memory in retrieved_memories:
            memory.retrieval_count += 1
            memory.last_accessed = datetime.datetime.now().strftime("%Y%m%d%H%M")
        
        return retrieved_memories
    
    def format_memories_as_context(self, memories: List[Memory], include_code: bool = True) -> str:
        """
        Format a list of memories as context for an LLM prompt
        
        Args:
            memories: List of Memory objects
            include_code: Whether to include code snippets
            
        Returns:
            Formatted string for inclusion in an LLM prompt
        """
        formatted = []
        for memory in memories:
            entry = f"[Memory {memory.id}]\n"
            entry += f"Content: {memory.content}\n"
            entry += f"Context: {memory.context}\n"
            entry += f"Keywords: {', '.join(memory.keywords)}\n"
            entry += f"Tags: {', '.join(memory.tags)}\n"
            
            if include_code and memory.faulty_code and memory.language:
                entry += f"Language: {memory.language}\n"
                entry += f"Faulty Code:\n```{memory.language}\n{memory.faulty_code}\n```\n"
                
                if memory.compiler_errors:
                    entry += f"Compiler Errors:\n"
                    for i, error in enumerate(memory.compiler_errors):
                        entry += f"{i+1}. {error}\n"
                
                if memory.fixed_code:
                    entry += f"Fixed Code:\n```{memory.language}\n{memory.fixed_code}\n```\n"
                    
            entry += f"Timestamp: {memory.timestamp}\n"
            formatted.append(entry)
        
        return "\n".join(formatted)
    
    def update_memory_code_fields(self, memory_id: str, compiler_errors=None, fixed_code=None) -> bool:
        """
        Update code-related fields of a memory.
        
        Args:
            memory_id: ID of the memory to update
            compiler_errors: List of compiler error messages (optional)
            fixed_code: Fixed version of the code (optional)
            
        Returns:
            True if successful, False otherwise
        """
        # Check if memory exists
        if memory_id not in self.memories:
            return False
        
        # Update memory object
        if compiler_errors is not None:
            self.memories[memory_id].compiler_errors = compiler_errors
            
        if fixed_code is not None:
            self.memories[memory_id].fixed_code = fixed_code
        
        # If using SQLite, also update database
        if self.use_sqlite and self.db_store:
            updates = {}
            if compiler_errors is not None:
                updates["compiler_errors"] = compiler_errors
            if fixed_code is not None:
                updates["fixed_code"] = fixed_code
                
            self.db_store.update_code_fields(memory_id, **updates)
        
        # Save to disk
        self._save_memories()
        
        return True
    
    def get_unfixed_memories(self, language=None) -> List[Memory]:
        """
        Get memories that don't have fixed code yet.
        
        Args:
            language: Optional filter by programming language
            
        Returns:
            List of Memory objects with unfixed code
        """
        if self.use_sqlite and self.db_store:
            # Use SQLite query for better performance
            memory_dicts = self.db_store.get_unfixed_memories(language)
            return [Memory.from_dict(m) for m in memory_dicts]
        else:
            # Filter in-memory
            result = []
            for memory in self.memories.values():
                if not memory.fixed_code:
                    if language is None or memory.language == language:
                        result.append(memory)
            return result

    def run(self, user_input: Dict[str, Any]) -> Dict[str, Any]:
        """
        Run the memory operation based on the command.
        
        Args:
            user_input: Dictionary containing the command and parameters.
                Expected keys vary by command:
                - "retrieve": requires "query", optional "k"
                - "add": requires "content", optional metadata
                - "delete": requires "memory_id"
                - "update_code": requires "memory_id", optional "compiler_errors", "fixed_code"
                - "get_unfixed": optional "language"
                - "status": no additional parameters required
        
        Returns:
            Dict with operation results
        """
        command = user_input.get("command", "").lower()
        
        try:
            if command == "retrieve":
                query = user_input.get("query", "")
                k = user_input.get("k", 5)
                
                if not query:
                    return {"status": "error", "message": "Query parameter is required for retrieve command"}
                
                memories = self.retrieve_memories(query, k)
                serialized_memories = []
                
                for memory in memories:
                    if hasattr(memory, 'to_dict'):
                        serialized_memories.append(memory.to_dict())
                    else:
                        serialized_memory = {
                            "id": memory.id,
                            "content": memory.content,
                            "keywords": memory.keywords,
                            "tags": memory.tags,
                            "timestamp": memory.timestamp,
                            "last_accessed": memory.last_accessed
                        }
                        serialized_memories.append(serialized_memory)
                
                return {
                    "status": "success",
                    "memories": serialized_memories,
                    "count": len(serialized_memories)
                }
            
            elif command == "add":
                content = user_input.get("content", "")
                
                if not content:
                    return {"status": "error", "message": "Content parameter is required for add command"}
                
                # Extract metadata from user_input excluding command and content
                metadata = {k: v for k, v in user_input.items() if k not in ["command", "content"]}
                
                memory_id = self.add_memory(content, **metadata)
                
                return {
                    "status": "success",
                    "memory_id": memory_id
                }
            
            elif command == "delete":
                memory_id = user_input.get("memory_id", "")
                
                if not memory_id:
                    return {"status": "error", "message": "Memory ID is required for delete command"}
                
                success = self.delete_memory(memory_id)
                
                if success:
                    return {
                        "status": "success",
                        "message": f"Memory {memory_id} deleted"
                    }
                else:
                    return {
                        "status": "error",
                        "message": f"Memory {memory_id} not found"
                    }
            
            elif command == "update_code":
                memory_id = user_input.get("memory_id", "")
                
                if not memory_id:
                    return {"status": "error", "message": "Memory ID is required for update_code command"}
                
                compiler_errors = user_input.get("compiler_errors")
                fixed_code = user_input.get("fixed_code")
                
                success = self.update_memory_code_fields(memory_id, compiler_errors, fixed_code)
                
                if success:
                    return {
                        "status": "success",
                        "message": f"Memory {memory_id} code fields updated"
                    }
                else:
                    return {
                        "status": "error",
                        "message": f"Memory {memory_id} not found"
                    }
            
            elif command == "get_unfixed":
                language = user_input.get("language")
                
                memories = self.get_unfixed_memories(language)
                serialized_memories = [memory.to_dict() for memory in memories]
                
                return {
                    "status": "success",
                    "memories": serialized_memories,
                    "count": len(serialized_memories)
                }
            
            elif command == "status":
                return {
                    "status": "success",
                    "total_memories": self.total_memories,
                    "last_error": self.last_error if hasattr(self, "last_error") else None
                }
            
            else:
                return {
                    "status": "error",
                    "message": f"Unknown command: {command}"
                }
        
        except Exception as e:
            error_message = str(e)
            # Store error for status reporting
            self.last_error = error_message
            return {"status": "error", "message": error_message}
