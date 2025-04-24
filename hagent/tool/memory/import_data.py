import json
import os
from pathlib import Path
from hagent.tool.memory.db_memory_store import SQLiteMemoryStore

def import_json_to_sqlite(json_path: str, db_path: str = None):
    """
    Import memory data from JSON file to SQLite database.
    
    Args:
        json_path: Path to the JSON file
        db_path: Path to the SQLite database (optional)
    """
    # Ensure JSON file exists
    if not os.path.exists(json_path):
        raise FileNotFoundError(f"JSON file not found: {json_path}")
    
    # Load JSON data
    with open(json_path, 'r') as f:
        memories = json.load(f)
    
    # Initialize SQLite store
    db_store = SQLiteMemoryStore(db_path)
    
    # Import each memory
    for memory in memories:
        # Ensure required code fields exist, even if empty
        if "faulty_code" not in memory:
            memory["faulty_code"] = ""
        if "fixed_code" not in memory:
            memory["fixed_code"] = ""
        if "language" not in memory:
            memory["language"] = ""
        if "compiler_errors" not in memory:
            memory["compiler_errors"] = []
            
        db_store.add_memory(memory)
    
    print(f"Imported {len(memories)} memories to {db_store.db_path}")
    db_store.close()

def export_sqlite_to_json(db_path: str, json_path: str = None):
    """
    Export memory data from SQLite database to JSON file.
    
    Args:
        db_path: Path to the SQLite database
        json_path: Path to the output JSON file (optional)
    """
    # Ensure database exists
    if not os.path.exists(db_path):
        raise FileNotFoundError(f"Database file not found: {db_path}")
    
    # Initialize SQLite store
    db_store = SQLiteMemoryStore(db_path)
    
    # Get all memories
    memories = db_store.get_all_memories()
    
    # Determine output path
    if json_path is None:
        json_path = str(Path(db_path).with_suffix('.json'))
    
    # Export to JSON
    with open(json_path, 'w') as f:
        json.dump(memories, f, indent=2)
    
    print(f"Exported {len(memories)} memories to {json_path}")
    db_store.close()
    
    return json_path

if __name__ == "__main__":
    # Default paths
    json_path = str(Path(__file__).parent / "data" / "sample_memories.json")
    db_path = str(Path(__file__).parent / "data" / "memory.db")
    
    # Import data
    import_json_to_sqlite(json_path, db_path)
