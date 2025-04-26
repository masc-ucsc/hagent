import sqlite3
import json
import os
from pathlib import Path
from typing import List, Dict, Optional, Any

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
        
        # Enable foreign keys
        self.conn.execute("PRAGMA foreign_keys = ON")
        
        # Create or update tables
        self.create_tables()
        self.upgrade_schema_if_needed()
    
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
        """
        cursor = self.conn.cursor()
        
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
        
        # Extract lists
        keywords = memory_data.get("keywords", [])
        tags = memory_data.get("tags", [])
        links = memory_data.get("links", [])
        
        # Other metadata
        metadata = {}
        for key, value in memory_data.items():
            if key not in ["id", "content", "context", "importance_score", 
                          "retrieval_count", "timestamp", "last_accessed", 
                          "category", "keywords", "tags", "links", 
                          "faulty_code", "fixed_code", "compiler_errors", "language"]:
                metadata[key] = value
        
        # Insert memory
        cursor.execute('''
        INSERT INTO memories 
        (id, content, context, importance_score, retrieval_count, timestamp, last_accessed, 
         category, faulty_code, fixed_code, compiler_errors, language, metadata)
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
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
        
        self.conn.commit()
        return memory_id
    
    def get_memory(self, memory_id: str) -> Optional[Dict]:
        """
        Get a memory by ID.
        
        Args:
            memory_id: ID of the memory to retrieve
            
        Returns:
            Memory data as a dictionary or None if not found
        """
        cursor = self.conn.cursor()
        
        # Get memory data
        cursor.execute('''
        SELECT id, content, context, importance_score, retrieval_count, timestamp, last_accessed, 
               category, faulty_code, fixed_code, compiler_errors, language, metadata
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
            "language": memory_row[11]
        }
        
        # Add metadata
        if memory_row[12]:
            metadata = json.loads(memory_row[12])
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
    
    def get_all_memories(self) -> List[Dict]:
        """
        Get all memories.
        
        Returns:
            List of memory dictionaries
        """
        cursor = self.conn.cursor()
        
        # Get all memory IDs
        cursor.execute('SELECT id FROM memories')
        memory_ids = [row[0] for row in cursor.fetchall()]
        
        # Get full memory data for each ID
        return [self.get_memory(memory_id) for memory_id in memory_ids]
    
    def update_memory(self, memory_id: str, updates: Dict) -> bool:
        """
        Update a memory.
        
        Args:
            memory_id: ID of the memory to update
            updates: Dictionary of fields to update
            
        Returns:
            True if successful, False otherwise
        """
        cursor = self.conn.cursor()
        
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
        
        self.conn.commit()
        return True
    
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
        cursor = self.conn.cursor()
        
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
        
        self.conn.commit()
        return True
    
    def get_unfixed_memories(self, language=None) -> List[Dict]:
        """
        Get memories that don't have fixed code yet.
        
        Args:
            language: Optional filter by programming language
            
        Returns:
            List of memory dictionaries with unfixed code
        """
        cursor = self.conn.cursor()
        
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
    
    def delete_memory(self, memory_id: str) -> bool:
        """
        Delete a memory.
        
        Args:
            memory_id: ID of the memory to delete
            
        Returns:
            True if successful, False otherwise
        """
        cursor = self.conn.cursor()
        
        # Check if memory exists
        cursor.execute('SELECT id FROM memories WHERE id = ?', (memory_id,))
        if not cursor.fetchone():
            return False
        
        # Delete memory (cascade will delete related data)
        cursor.execute('DELETE FROM memories WHERE id = ?', (memory_id,))
        
        self.conn.commit()
        return True
    
    def search_memories(self, query: str, limit: int = 10) -> List[Dict]:
        """
        Basic text search for memories.
        
        Args:
            query: Search query
            limit: Maximum number of results
            
        Returns:
            List of matching memory dictionaries
        """
        cursor = self.conn.cursor()
        
        # Simple FTS using LIKE - in a real implementation you would use
        # proper full-text search or vector embeddings
        cursor.execute('''
        SELECT id
        FROM memories
        WHERE content LIKE ? OR context LIKE ? OR faulty_code LIKE ? OR fixed_code LIKE ?
        LIMIT ?
        ''', (f'%{query}%', f'%{query}%', f'%{query}%', f'%{query}%', limit))
        
        memory_ids = [row[0] for row in cursor.fetchall()]
        
        # Also search in keywords
        cursor.execute('''
        SELECT DISTINCT memory_id
        FROM keywords
        WHERE keyword LIKE ?
        LIMIT ?
        ''', (f'%{query}%', limit))
        
        memory_ids.extend([row[0] for row in cursor.fetchall()])
        
        # Remove duplicates and respect limit
        memory_ids = list(set(memory_ids))[:limit]
        
        # Get full memory data
        return [self.get_memory(memory_id) for memory_id in memory_ids]
    
    def close(self):
        """Close the database connection."""
        if self.conn:
            self.conn.close()