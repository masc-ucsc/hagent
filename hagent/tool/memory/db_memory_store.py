import sqlite3
import json
import os
from pathlib import Path
from typing import List, Dict, Optional, Any, Union, Tuple
import logging

class SQLiteMemoryStore:
    """SQLite-based memory storage for FewShotMemory."""
    
    def __init__(self, db_path: str = None):
        """Initialize SQLite memory store."""
        if db_path is None:
            db_path = str(Path(__file__).parent / "data" / "memory.db")
        
        # Ensure directory exists
        os.makedirs(os.path.dirname(db_path), exist_ok=True)
        
        self.db_path = db_path
        self.conn = sqlite3.connect(db_path)
        self.logger = logging.getLogger(__name__)
        
        # Enable foreign keys
        self.conn.execute("PRAGMA foreign_keys = ON")
        
        # Create or update tables
        self.create_tables()
        self.upgrade_schema_if_needed()
    
    def _get_connection(self):
        """Get a SQLite connection, creating a new one if needed."""
        if hasattr(self, 'conn') and self.conn:
            try:
                # Test the connection
                self.conn.execute("SELECT 1")
                return self.conn
            except sqlite3.Error:
                # Connection is broken, create a new one
                self.conn.close()
        
        # Create a new connection
        self.conn = sqlite3.connect(self.db_path)
        self.conn.execute("PRAGMA foreign_keys = ON")
        return self.conn
    
    def create_tables(self):
        """Create necessary tables if they don't exist."""
        cursor = self.conn.cursor()
        
        # Create memories table with faulty_code, fixed_code, and compiler_errors columns
        cursor.execute('''
        CREATE TABLE IF NOT EXISTS memories (
            id TEXT PRIMARY KEY,
            content TEXT NOT NULL,
            context TEXT,
            importance_score REAL DEFAULT 1.0,
            retrieval_count INTEGER DEFAULT 0,
            timestamp TEXT,
            last_accessed TEXT,
            category TEXT,
            faulty_code TEXT,
            fixed_code TEXT,
            compiler_errors TEXT,
            language TEXT,
            bug_type TEXT,
            metadata TEXT
        )
        ''')
        
        # Create keywords table (many-to-many relationship)
        cursor.execute('''
        CREATE TABLE IF NOT EXISTS keywords (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            memory_id TEXT,
            keyword TEXT,
            FOREIGN KEY (memory_id) REFERENCES memories (id) ON DELETE CASCADE
        )
        ''')
        
        # Create tags table (many-to-many relationship)
        cursor.execute('''
        CREATE TABLE IF NOT EXISTS tags (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            memory_id TEXT,
            tag TEXT,
            FOREIGN KEY (memory_id) REFERENCES memories (id) ON DELETE CASCADE
        )
        ''')
        
        # Create links table (many-to-many relationship)
        cursor.execute('''
        CREATE TABLE IF NOT EXISTS links (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            source_id TEXT,
            target_id TEXT,
            FOREIGN KEY (source_id) REFERENCES memories (id) ON DELETE CASCADE,
            FOREIGN KEY (target_id) REFERENCES memories (id) ON DELETE CASCADE
        )
        ''')
        
        self.conn.commit()
    
    def upgrade_schema_if_needed(self):
        """Check if schema needs upgrading and add missing columns."""
        cursor = self.conn.cursor()
        
        # Get column info for memories table
        cursor.execute("PRAGMA table_info(memories)")
        columns = {row[1]: row for row in cursor.fetchall()}
        
        # Check for missing columns and add them if needed
        try:
            if "faulty_code" not in columns:
                print("Adding faulty_code column to memories table")
                cursor.execute("ALTER TABLE memories ADD COLUMN faulty_code TEXT")
                
            if "fixed_code" not in columns:
                print("Adding fixed_code column to memories table")
                cursor.execute("ALTER TABLE memories ADD COLUMN fixed_code TEXT")
                
            if "language" not in columns:
                print("Adding language column to memories table")
                cursor.execute("ALTER TABLE memories ADD COLUMN language TEXT")
                
            if "compiler_errors" not in columns:
                print("Adding compiler_errors column to memories table")
                cursor.execute("ALTER TABLE memories ADD COLUMN compiler_errors TEXT")
                
            if "bug_type" not in columns:
                print("Adding bug_type column to memories table")
                cursor.execute("ALTER TABLE memories ADD COLUMN bug_type TEXT")
                
            self.conn.commit()
            print("Database schema upgraded successfully")
        except Exception as e:
            print(f"Error upgrading database schema: {e}")
    
    def add_memory(self, memory_data: Dict) -> str:
        """
        Add a memory to the database.
        
        Args:
            memory_data: Dictionary containing memory data
            
        Returns:
            ID of the added memory
        
        Note:
            Extended fields not in the schema (like line_number, error_type)
            are automatically stored in the metadata JSON field.
        """
        conn = self._get_connection()
        cursor = conn.cursor()
        
        try:
            # Extract fields
            memory_id = memory_data.get("id", None)
            content = memory_data.get("content", "")
            context = memory_data.get("context", "")
            importance_score = memory_data.get("importance_score", 1.0)
            retrieval_count = memory_data.get("retrieval_count", 0)
            timestamp = memory_data.get("timestamp", "")
            last_accessed = memory_data.get("last_accessed", "")
            category = memory_data.get("category", "")
            faulty_code = memory_data.get("faulty_code", "")
            fixed_code = memory_data.get("fixed_code", "")
            compiler_errors = json.dumps(memory_data.get("compiler_errors", []))
            language = memory_data.get("language", "")
            
            # Extract bug_type from error_type or use default
            bug_type = memory_data.get("bug_type", memory_data.get("error_type", ""))
            
            # Extract lists
            keywords = memory_data.get("keywords", [])
            tags = memory_data.get("tags", [])
            links = memory_data.get("links", [])
            
            # Other metadata - including extended fields like line_number and error_type
            metadata = {}
            core_fields = {
                "id", "content", "context", "importance_score", 
                "retrieval_count", "timestamp", "last_accessed", 
                "category", "keywords", "tags", "links", 
                "faulty_code", "fixed_code", "compiler_errors", "language",
                "bug_type", "error_type"
            }
            
            for key, value in memory_data.items():
                if key not in core_fields:
                    metadata[key] = value
            
            # Insert memory
            cursor.execute('''
            INSERT INTO memories 
            (id, content, context, importance_score, retrieval_count, timestamp, last_accessed, 
             category, faulty_code, fixed_code, compiler_errors, language, bug_type, metadata)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            ''', (
                memory_id, 
                content, 
                context, 
                importance_score, 
                retrieval_count, 
                timestamp, 
                last_accessed, 
                category,
                faulty_code,
                fixed_code,
                compiler_errors,
                language,
                bug_type,
                json.dumps(metadata)
            ))
            
            # If memory_id was None, get the auto-generated ID
            if memory_id is None:
                memory_id = cursor.lastrowid
            
            # Insert keywords
            for keyword in keywords:
                cursor.execute('''
                INSERT INTO keywords (memory_id, keyword)
                VALUES (?, ?)
                ''', (memory_id, keyword))
            
            # Insert tags
            for tag in tags:
                cursor.execute('''
                INSERT INTO tags (memory_id, tag)
                VALUES (?, ?)
                ''', (memory_id, tag))
            
            # Insert links
            for link in links:
                cursor.execute('''
                INSERT INTO links (source_id, target_id)
                VALUES (?, ?)
                ''', (memory_id, link))
            
            conn.commit()
            return memory_id
            
        except Exception as e:
            self.logger.error(f"Error adding memory: {e}")
            conn.rollback()
            return ""
    
    def get_memory(self, memory_id: str) -> Optional[Dict]:
        """
        Get a memory by ID.
        
        Args:
            memory_id: ID of the memory to retrieve
            
        Returns:
            Memory data as a dictionary or None if not found
        """
        conn = self._get_connection()
        cursor = conn.cursor()
        
        try:
            # Get memory data
            cursor.execute('''
            SELECT id, content, context, importance_score, retrieval_count, timestamp, last_accessed, 
                   category, faulty_code, fixed_code, compiler_errors, language, bug_type, metadata
            FROM memories
            WHERE id = ?
            ''', (memory_id,))
            
            memory_row = cursor.fetchone()
            if not memory_row:
                return None
            
            # Create memory dictionary
            memory_data = {
                "id": memory_row[0],
                "content": memory_row[1],
                "context": memory_row[2],
                "importance_score": memory_row[3],
                "retrieval_count": memory_row[4],
                "timestamp": memory_row[5],
                "last_accessed": memory_row[6],
                "category": memory_row[7],
                "faulty_code": memory_row[8],
                "fixed_code": memory_row[9],
                "compiler_errors": json.loads(memory_row[10]) if memory_row[10] else [],
                "language": memory_row[11],
                "bug_type": memory_row[12]
            }
            
            # Add metadata
            if memory_row[13]:
                metadata = json.loads(memory_row[13])
                memory_data.update(metadata)
            
            # Get keywords
            cursor.execute('''
            SELECT keyword
            FROM keywords
            WHERE memory_id = ?
            ''', (memory_id,))
            memory_data["keywords"] = [row[0] for row in cursor.fetchall()]
            
            # Get tags
            cursor.execute('''
            SELECT tag
            FROM tags
            WHERE memory_id = ?
            ''', (memory_id,))
            memory_data["tags"] = [row[0] for row in cursor.fetchall()]
            
            # Get links
            cursor.execute('''
            SELECT target_id
            FROM links
            WHERE source_id = ?
            ''', (memory_id,))
            memory_data["links"] = [row[0] for row in cursor.fetchall()]
            
            return memory_data
            
        except Exception as e:
            self.logger.error(f"Error getting memory {memory_id}: {e}")
            return None
    
    def get_all_memories(self) -> List[Dict]:
        """
        Get all memories.
        
        Returns:
            List of memory dictionaries
        """
        conn = self._get_connection()
        cursor = conn.cursor()
        
        try:
            # Get all memory IDs
            cursor.execute('SELECT id FROM memories')
            memory_ids = [row[0] for row in cursor.fetchall()]
            
            # Get full memory data for each ID
            return [self.get_memory(memory_id) for memory_id in memory_ids]
            
        except Exception as e:
            self.logger.error(f"Error getting all memories: {e}")
            return []
    
    def update_memory(self, memory_id: str, updates: Dict) -> bool:
        """
        Update a memory.
        
        Args:
            memory_id: ID of the memory to update
            updates: Dictionary of fields to update
            
        Returns:
            True if successful, False otherwise
        """
        conn = self._get_connection()
        cursor = conn.cursor()
        
        try:
            # Check if memory exists
            cursor.execute('SELECT id FROM memories WHERE id = ?', (memory_id,))
            if not cursor.fetchone():
                return False
            
            # Update simple fields
            fields = []
            values = []
            
            for field in ["content", "context", "importance_score", "retrieval_count", 
                         "timestamp", "last_accessed", "category", "faulty_code", 
                         "fixed_code", "language"]:
                if field in updates:
                    fields.append(f"{field} = ?")
                    values.append(updates[field])
            
            # Special handling for compiler_errors (JSON serialization)
            if "compiler_errors" in updates:
                fields.append("compiler_errors = ?")
                values.append(json.dumps(updates["compiler_errors"]))
            
            if fields:
                cursor.execute(f'''
                UPDATE memories
                SET {", ".join(fields)}
                WHERE id = ?
                ''', values + [memory_id])
            
            # Update keywords if provided
            if "keywords" in updates:
                # Delete existing keywords
                cursor.execute('DELETE FROM keywords WHERE memory_id = ?', (memory_id,))
                
                # Add new keywords
                for keyword in updates["keywords"]:
                    cursor.execute('''
                    INSERT INTO keywords (memory_id, keyword)
                    VALUES (?, ?)
                    ''', (memory_id, keyword))
            
            # Update tags if provided
            if "tags" in updates:
                # Delete existing tags
                cursor.execute('DELETE FROM tags WHERE memory_id = ?', (memory_id,))
                
                # Add new tags
                for tag in updates["tags"]:
                    cursor.execute('''
                    INSERT INTO tags (memory_id, tag)
                    VALUES (?, ?)
                    ''', (memory_id, tag))
            
            # Update links if provided
            if "links" in updates:
                # Delete existing links
                cursor.execute('DELETE FROM links WHERE source_id = ?', (memory_id,))
                
                # Add new links
                for link in updates["links"]:
                    cursor.execute('''
                    INSERT INTO links (source_id, target_id)
                    VALUES (?, ?)
                    ''', (memory_id, link))
            
            conn.commit()
            return True
            
        except Exception as e:
            self.logger.error(f"Error updating memory {memory_id}: {e}")
            conn.rollback()
            return False
    
    def update_code_fields(self, memory_id: str, compiler_errors=None, fixed_code=None) -> bool:
        """
        Update only code-related fields of a memory.
        
        Args:
            memory_id: ID of the memory to update
            compiler_errors: List of compiler error messages (optional)
            fixed_code: Fixed version of the code (optional)
            
        Returns:
            True if successful, False otherwise
        """
        conn = self._get_connection()
        cursor = conn.cursor()
        
        try:
            # Check if memory exists
            cursor.execute('SELECT id FROM memories WHERE id = ?', (memory_id,))
            if not cursor.fetchone():
                return False
            
            # Build update query based on provided fields
            fields = []
            values = []
            
            if compiler_errors is not None:
                fields.append("compiler_errors = ?")
                values.append(json.dumps(compiler_errors))
                
            if fixed_code is not None:
                fields.append("fixed_code = ?")
                values.append(fixed_code)
                
            if not fields:
                # Nothing to update
                return True
                
            # Execute update
            cursor.execute(f'''
            UPDATE memories
            SET {", ".join(fields)}
            WHERE id = ?
            ''', values + [memory_id])
            
            conn.commit()
            return True
            
        except Exception as e:
            self.logger.error(f"Error updating code fields for memory {memory_id}: {e}")
            conn.rollback()
            return False
    
    def get_unfixed_memories(self, language=None) -> List[Dict]:
        """
        Get memories that don't have fixed code yet.
        
        Args:
            language: Optional filter by programming language
            
        Returns:
            List of memory dictionaries with unfixed code
        """
        conn = self._get_connection()
        cursor = conn.cursor()
        
        try:
            if language:
                cursor.execute('''
                SELECT id FROM memories 
                WHERE fixed_code = '' OR fixed_code IS NULL
                AND language = ?
                ''', (language,))
            else:
                cursor.execute('''
                SELECT id FROM memories 
                WHERE fixed_code = '' OR fixed_code IS NULL
                ''')
                
            memory_ids = [row[0] for row in cursor.fetchall()]
            
            # Get full memory data for each ID
            return [self.get_memory(memory_id) for memory_id in memory_ids]
            
        except Exception as e:
            self.logger.error(f"Error getting unfixed memories: {e}")
            return []
    
    def delete_memory(self, memory_id: str) -> bool:
        """
        Delete a memory.
        
        Args:
            memory_id: ID of the memory to delete
            
        Returns:
            True if successful, False otherwise
        """
        conn = self._get_connection()
        cursor = conn.cursor()
        
        try:
            # Check if memory exists
            cursor.execute('SELECT id FROM memories WHERE id = ?', (memory_id,))
            if not cursor.fetchone():
                return False
            
            # Delete memory (cascade will delete related data)
            cursor.execute('DELETE FROM memories WHERE id = ?', (memory_id,))
            
            conn.commit()
            return True
            
        except Exception as e:
            self.logger.error(f"Error deleting memory {memory_id}: {e}")
            conn.rollback()
            return False
    
    def search_memories(self, query: str, filter_query: Dict = None, k: int = 10) -> List[Dict]:
        """
        Basic text search for memories.
        
        Args:
            query: Search query
            filter_query: Optional dictionary of metadata filters
            k: Maximum number of results (previously called limit)
            
        Returns:
            List of matching memory dictionaries
        """
        conn = self._get_connection()
        cursor = conn.cursor()
        
        try:
            # Start building the query
            sql_query = '''
            SELECT id
            FROM memories
            WHERE (content LIKE ? OR context LIKE ? OR faulty_code LIKE ? OR fixed_code LIKE ?)
            '''
            
            params = [f'%{query}%', f'%{query}%', f'%{query}%', f'%{query}%']
            
            # Add metadata filters if provided
            if filter_query:
                for key, value in filter_query.items():
                    if key == 'language':
                        sql_query += " AND language = ?"
                        params.append(value)
                    elif key == 'bug_type':
                        sql_query += " AND bug_type = ?"
                        params.append(value)
                    elif key == 'category':
                        sql_query += " AND category = ?"
                        params.append(value)
                    elif key != 'embedding_index':  # Skip embedding_index as it's handled elsewhere
                        sql_query += f" AND metadata LIKE ?"
                        params.append(f'%"{key}":"{value}"%')
            
            # Add limit
            sql_query += " LIMIT ?"
            params.append(k)
            
            # Execute the query
            cursor.execute(sql_query, params)
            memory_ids = [row[0] for row in cursor.fetchall()]
            
            # Also search in keywords
            keyword_query = '''
            SELECT DISTINCT memory_id
            FROM keywords
            WHERE keyword LIKE ?
            '''
            
            keyword_params = [f'%{query}%']
            
            # Add metadata filters for keywords query too
            if filter_query and 'language' in filter_query:
                keyword_query += " AND memory_id IN (SELECT id FROM memories WHERE language = ?)"
                keyword_params.append(filter_query['language'])
            
            keyword_query += " LIMIT ?"
            keyword_params.append(k)
            
            cursor.execute(keyword_query, keyword_params)
            memory_ids.extend([row[0] for row in cursor.fetchall()])
            
            # Remove duplicates and respect limit
            memory_ids = list(set(memory_ids))[:k]
            
            # Get full memory data
            memories = []
            for memory_id in memory_ids:
                memory = self.get_memory(memory_id)
                if memory:
                    memories.append(memory)
                    
            return memories
            
        except Exception as e:
            self.logger.error(f"Error searching memories: {str(e)}")
            return []
    
    def find_similar_bugs(self, code: str, language: str, compiler_errors: str = None, 
                          bug_type: str = None, k: int = 3, threshold: float = 0.0,
                          exact_match: bool = False) -> List[Dict[str, Any]]:
        """
        Find memories with similar bug patterns based on code, errors, and other parameters.
        
        Args:
            code: The faulty code to find similar bugs for
            language: Programming language of the code
            compiler_errors: Compiler/interpreter error messages (optional)
            bug_type: Type of bug to filter by (optional)
            k: Maximum number of results to return
            threshold: Minimum similarity score (0-1)
            exact_match: Whether to only return exact matches
            
        Returns:
            List of memories with similarity scores
        """
        conn = self._get_connection()
        cursor = conn.cursor()
        
        try:
            # Build the SQL query
            query = "SELECT * FROM memories WHERE language = ?"
            params = [language]
            
            if bug_type:
                query += " AND bug_type = ?"
                params.append(bug_type)
            
            # Execute the query
            cursor.execute(query, params)
            memories = cursor.fetchall()
            
            # Extract column names
            column_names = [desc[0] for desc in cursor.description]
            
            # Convert to list of dictionaries
            results = []
            for row in memories:
                memory_dict = dict(zip(column_names, row))
                
                # Calculate similarity score
                similarity = 0.0
                
                # Simple string matching for exact match
                if exact_match:
                    # If code is an exact match, give it a perfect score
                    if memory_dict.get('faulty_code') == code:
                        similarity = 1.0
                    # If there's a compiler error and it matches exactly, consider it close
                    elif compiler_errors and memory_dict.get('compiler_errors') == compiler_errors:
                        similarity = 0.9
                    else:
                        similarity = 0.0
                else:
                    # Calculate code similarity (60% weight)
                    code_similarity = self._calculate_text_similarity(
                        code, memory_dict.get('faulty_code', ''))
                    
                    # Calculate error similarity (40% weight) if compiler errors are provided
                    error_similarity = 0.0
                    if compiler_errors and memory_dict.get('compiler_errors'):
                        error_similarity = self._calculate_text_similarity(
                            compiler_errors, memory_dict.get('compiler_errors', ''))
                    
                    # Weighted average of similarities
                    if compiler_errors:
                        similarity = (code_similarity * 0.6) + (error_similarity * 0.4)
                    else:
                        similarity = code_similarity
                
                # Only include results above threshold
                if similarity >= threshold:
                    memory_dict['similarity'] = similarity
                    results.append(memory_dict)
            
            # Sort by similarity and limit to k results
            results.sort(key=lambda x: x['similarity'], reverse=True)
            return results[:k]
            
        except Exception as e:
            self.logger.error(f"Error finding similar bugs: {e}")
            return []
    
    def _calculate_text_similarity(self, text1: str, text2: str) -> float:
        """
        Calculate similarity between two text strings.
        
        Args:
            text1: First text string
            text2: Second text string
            
        Returns:
            Similarity score between 0 and 1
        """
        if not text1 or not text2:
            return 0.0
        
        # Convert to sets of words for simple Jaccard similarity
        set1 = set(text1.lower().split())
        set2 = set(text2.lower().split())
        
        # Calculate Jaccard similarity: intersection over union
        intersection = len(set1.intersection(set2))
        union = len(set1.union(set2))
        
        if union == 0:
            return 0.0
        
        return intersection / union
    
    def close(self):
        """Close the database connection."""
        if self.conn:
            self.conn.close()