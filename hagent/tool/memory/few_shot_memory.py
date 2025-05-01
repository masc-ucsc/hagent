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
import warnings

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


class SimpleEmbeddingRetriever:
    """Simple retrieval system using only text embeddings."""
    
    def __init__(self, model_name: str = 'all-MiniLM-L6-v2'):
        """Initialize the simple embedding retriever."""
        try:
            self.model = SentenceTransformer(model_name)
            self.corpus = []
            self.embeddings = None
            self.document_ids = {}  # Map document content to its index
            self.initialized = True
        except Exception as e:
            print(f"Error initializing SentenceTransformer: {e}")
            self.initialized = False
    
    def add_documents(self, documents: List[str]):
        """Add documents to the retriever."""
        if not self.initialized:
            return
            
        # Reset if no existing documents
        if not self.corpus:
            self.corpus = documents
            self.embeddings = self.model.encode(documents)
            self.document_ids = {doc: idx for idx, doc in enumerate(documents)}
        else:
            # Append new documents
            start_idx = len(self.corpus)
            self.corpus.extend(documents)
            new_embeddings = self.model.encode(documents)
            if self.embeddings is None:
                self.embeddings = new_embeddings
            else:
                self.embeddings = np.vstack([self.embeddings, new_embeddings])
            for idx, doc in enumerate(documents):
                self.document_ids[doc] = start_idx + idx
    
    def search(self, query: str, k: int = 5) -> List[Dict]:
        """Search for similar documents using cosine similarity."""
        if not self.initialized or not self.corpus:
            return []
            
        # Encode query
        query_embedding = self.model.encode([query])[0]
        
        # Calculate cosine similarities
        similarities = cosine_similarity([query_embedding], self.embeddings)[0]
        
        # Get top k results
        top_k_indices = np.argsort(similarities)[-k:][::-1]
        top_k_scores = similarities[top_k_indices]
        
        # Return results as dict with score
        results = []
        for idx, score in zip(top_k_indices, top_k_scores):
            if idx < len(self.corpus):
                results.append({
                    'id': str(idx),  # Convert to string for consistency
                    'content': self.corpus[idx],
                    'score': float(score),
                    'retrieval_method': 'semantic'
                })
        
        return results
    
    def save(self, retriever_file: str, embeddings_file: str):
        """Save retriever state to disk."""
        if not self.initialized:
            return
            
        # Save embeddings using numpy
        if self.embeddings is not None:
            np.save(embeddings_file, self.embeddings)
        
        # Save other attributes
        state = {
            'corpus': self.corpus,
            'document_ids': self.document_ids,
            'model_name': self.model.__class__.__name__
        }
        with open(retriever_file, 'wb') as f:
            import pickle
            pickle.dump(state, f)
    
    def load(self, retriever_file: str, embeddings_file: str):
        """Load retriever state from disk."""
        if not self.initialized:
            return
            
        # Load embeddings
        if os.path.exists(embeddings_file):
            self.embeddings = np.load(embeddings_file)
        
        # Load other attributes
        if os.path.exists(retriever_file):
            import pickle
            with open(retriever_file, 'rb') as f:
                state = pickle.load(f)
                self.corpus = state.get('corpus', [])
                self.document_ids = state.get('document_ids', {})
        
        return self


class HybridRetriever:
    """A retriever that combines lexical and semantic search"""
    
    def __init__(self, db_store, embedding_retriever=None):
        self.db_store = db_store
        self.embedding_retriever = embedding_retriever
        
    def retrieve(self, query: str, code: str = None, errors: List[str] = None, 
                 language: str = None, bug_type: str = None, k: int = 3) -> List[Dict]:
        """
        Retrieve relevant memories using a combination of lexical and semantic search.
        
        Args:
            query: The search query
            code: Optional code snippet to search for similar bugs
            errors: Optional list of error messages
            language: Programming language filter
            bug_type: Bug type filter
            k: Number of results to return
            
        Returns:
            List of memories
        """
        results = []
        
        # Create filter_query from language and bug_type
        filter_query = {}
        if language:
            filter_query['language'] = language
        if bug_type:
            filter_query['bug_type'] = bug_type
        
        # Try lexical search first
        try:
            # If we have code and errors, use find_similar_bugs for a specialized bug finder
            if code and errors and self.db_store:
                compiler_errors = '\n'.join(errors) if isinstance(errors, list) else errors
                lexical_results = self.db_store.find_similar_bugs(
                    code=code, 
                    language=language or '', 
                    compiler_errors=compiler_errors,
                    bug_type=bug_type,
                    k=k
                )
                if lexical_results:
                    for result in lexical_results:
                        result['retrieval_method'] = 'lexical_bug_finder'
                        result['score'] = result.get('similarity', 0.5)  # Use similarity as score if available
                    results.extend(lexical_results)
            
            # General lexical search based on query
            if self.db_store:
                search_results = self.db_store.search_memories(query, filter_query, k)
                if search_results:
                    for result in search_results:
                        if not any(r.get('id') == result.get('id') for r in results):  # Avoid duplicates
                            result['retrieval_method'] = 'lexical'
                            result['score'] = 0.4  # Default score for lexical results
                            results.append(result)
        except Exception as e:
            warnings.warn(f"Lexical search failed: {str(e)}")
        
        # Try semantic search if an embedding retriever is available
        if self.embedding_retriever:
            try:
                # Create a combined query that includes the main query, some code, and some errors
                combined_query = query
                if code:
                    # Include first 200 chars of code in the query
                    code_sample = code[:200]
                    combined_query += f" {code_sample}"
                
                if errors and len(errors) > 0:
                    # Include first error message in the query
                    error_sample = errors[0][:200] if errors[0] else ""
                    combined_query += f" {error_sample}"
                
                semantic_results = self.embedding_retriever.search(combined_query, k)
                
                if semantic_results:
                    for result in semantic_results:
                        # Check if we already have this result
                        if not any(r.get('id') == result.get('id') for r in results):
                            result['retrieval_method'] = 'semantic'
                            # Score is already set by embedding retriever
                            results.append(result)
            except Exception as e:
                warnings.warn(f"Semantic search failed: {str(e)}")
        
        # Sort by score and return top k
        results = sorted(results, key=lambda x: x.get('score', 0), reverse=True)
        return results[:k]


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
        
        # Set up retrievers
        self.retriever = SimpleEmbeddingRetriever(model_name)
        
        # Initialize hybrid retriever with db_store and retriever
        self.hybrid_retriever = HybridRetriever(self.db_store, self.retriever)
        
        # Set paths for embeddings
        self.embeddings_file = os.path.join(memory_dir, f"{name}_embeddings.npy")
        self.retriever_file = os.path.join(memory_dir, f"{name}_retriever.pkl")
        
        # Try to load embeddings
        if os.path.exists(self.embeddings_file):
            try:
                self.retriever.embeddings = np.load(self.embeddings_file)
                print(f"Loaded embeddings from {self.embeddings_file}")
            except Exception as e:
                print(f"Error loading embeddings: {e}")
        
        # Metadata
        self.total_memories = 0
        self.last_error = None
        
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
            if os.path.exists(self.retriever_file):
                try:
                    with open(self.retriever_file, 'rb') as f:
                        state = pickle.load(f)
                        self.retriever = SimpleEmbeddingRetriever(state['model_name'])
                        self.retriever.embeddings = state['embeddings']
                        self.retriever.corpus = state['corpus']
                        self.retriever.document_ids = state['document_ids']
                        self.total_memories = len(self.retriever.corpus)
                except Exception as e:
                    self.last_error = f"Error loading retriever from file: {str(e)}"
                    self.retriever = SimpleEmbeddingRetriever()
                    self.total_memories = 0
    
    def _save_memories(self) -> None:
        """Save memories to disk or database"""
        try:
            if self.use_sqlite and self.db_store:
                # We don't need to save to database here, as we update it in real-time
                # with add_memory and delete_memory operations
                pass
            else:
                # Save to file
                with open(self.retriever_file, 'wb') as f:
                    pickle.dump({
                        'model_name': self.retriever.model.__class__.__name__,
                        'corpus': self.retriever.corpus,
                        'document_ids': self.retriever.document_ids,
                        'embeddings': self.retriever.embeddings
                    }, f)
            
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
        self.retriever = SimpleEmbeddingRetriever()
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
    
    def retrieve_memories(self, query: str, code: str = "", errors: List[str] = [], 
                        language: str = None, bug_type: str = None, k: int = 3) -> List[Memory]:
        """
        Retrieve memories relevant to the query using hybrid retrieval.
        
        Args:
            query: The search query
            code: Optional code snippet to match
            errors: Optional error messages to match
            language: Optional language filter
            bug_type: Optional bug type filter
            k: Number of memories to retrieve
            
        Returns:
            List of Memory objects
        """
        if not self.memories:
            return []
        
        # Use hybrid retriever if available
        try:
            if hasattr(self, 'hybrid_retriever') and self.hybrid_retriever:
                memory_dicts = self.hybrid_retriever.retrieve(
                    query=query,
                    code=code,
                    errors=errors,
                    language=language,
                    bug_type=bug_type,
                    k=k
                )
                
                # Convert to Memory objects
                memories = []
                for memory_dict in memory_dicts:
                    memory_id = memory_dict.get("id")
                    if memory_id and memory_id in self.memories:
                        # Use existing memory object
                        memory = self.memories[memory_id]
                        # Update retrieval count
                        memory.retrieval_count += 1
                        memory.last_accessed = datetime.datetime.now().strftime("%Y%m%d%H%M")
                        memories.append(memory)
                    else:
                        # Create memory object from dict
                        try:
                            memory = Memory.from_dict(memory_dict)
                            memories.append(memory)
                        except Exception as e:
                            print(f"Error creating memory from dict: {e}")
                        
                return memories
        except Exception as e:
            print(f"Warning: Error using hybrid retriever: {e}")
            print("Falling back to basic retrieval...")
            
        # Fallback to simple retriever
        try:
            # Use basic search from SimpleEmbeddingRetriever
            search_results = self.retriever.search(query, k)
            
            # Convert to list of memories
            memories = []
            for result in search_results:
                result_id = result.get("id")
                if result_id and result_id.isdigit():
                    idx = int(result_id)
                    memories_list = list(self.memories.values())
                    if idx < len(memories_list):
                        memory = memories_list[idx]
                        # Update retrieval count
                        memory.retrieval_count += 1
                        memory.last_accessed = datetime.datetime.now().strftime("%Y%m%d%H%M")
                        memories.append(memory)
            
            return memories
        except Exception as e:
            print(f"Error in fallback retrieval: {e}")
            return []
    
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
