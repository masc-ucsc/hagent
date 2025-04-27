import json
import os
from pathlib import Path
from hagent.tool.memory.db_memory_store import SQLiteMemoryStore

def import_json_to_sqlite(json_path: str, db_path: str = None, verbose: bool = False, silent: bool = False):
    """
    Import memory data from JSON file to SQLite database.
    
    Args:
        json_path: Path to the JSON file
        db_path: Path to the SQLite database (optional)
        verbose: Whether to print verbose output
        silent: Whether to suppress non-essential output
    """
    # Ensure JSON file exists
    if not os.path.exists(json_path):
        raise FileNotFoundError(f"JSON file not found: {json_path}")
    
    # Load JSON data
    with open(json_path, 'r') as f:
        memories = json.load(f)
    
    if verbose and not silent:
        print(f"Loaded {len(memories)} memory entries from {json_path}")
    
    # Initialize SQLite store
    db_store = SQLiteMemoryStore(db_path)
    
    if verbose and not silent:
        print(f"Using database at: {db_store.db_path}")
    
    # Import each memory
    for i, memory in enumerate(memories):
        # Ensure required code fields exist, even if empty
        if "faulty_code" not in memory:
            memory["faulty_code"] = ""
        if "fixed_code" not in memory:
            memory["fixed_code"] = ""
        if "language" not in memory:
            memory["language"] = ""
        if "compiler_errors" not in memory:
            memory["compiler_errors"] = []
        
        # Handle additional fields that will be stored in metadata
        # These are new fields from the updated create_test_data.py
        expected_metadata_fields = [
            "line_number", 
            "error_type",
            "created_at"
        ]
        
        memory_id = db_store.add_memory(memory)
        
        if verbose and not silent and (i == 0 or i == len(memories) - 1 or i % 10 == 0):
            print(f"Imported memory {i+1}/{len(memories)}: {memory.get('content', '')[:50]}...")
            
    if not silent:
        print(f"Imported {len(memories)} memories to {db_store.db_path}")
        print(f"Note: Extended fields like 'line_number' and 'error_type' are stored in the metadata column")
    
    db_store.close()
    return len(memories)

def export_sqlite_to_json(db_path: str, json_path: str = None, verbose: bool = False, silent: bool = False):
    """
    Export memory data from SQLite database to JSON file.
    
    Args:
        db_path: Path to the SQLite database
        json_path: Path to the output JSON file (optional)
        verbose: Whether to print verbose output
        silent: Whether to suppress non-essential output
    """
    # Ensure database exists
    if not os.path.exists(db_path):
        raise FileNotFoundError(f"Database file not found: {db_path}")
    
    # Initialize SQLite store
    db_store = SQLiteMemoryStore(db_path)
    
    if verbose and not silent:
        print(f"Reading from database: {db_path}")
    
    # Get all memories
    memories = db_store.get_all_memories()
    
    if verbose and not silent:
        print(f"Retrieved {len(memories)} memory entries")
    
    # Determine output path
    if json_path is None:
        json_path = str(Path(db_path).with_suffix('.json'))
    
    # Export to JSON
    with open(json_path, 'w') as f:
        json.dump(memories, f, indent=2)
    
    if not silent:
        print(f"Exported {len(memories)} memories to {json_path}")
    
    db_store.close()
    return json_path

if __name__ == "__main__":
    import argparse
    
    parser = argparse.ArgumentParser(description="Import/Export memory data between JSON and SQLite")
    parser.add_argument("--import", dest="import_path", help="Import from JSON file to SQLite")
    parser.add_argument("--export", dest="export_path", help="Export from SQLite to JSON file")
    parser.add_argument("--db", help="Path to SQLite database (optional)")
    parser.add_argument("--output", help="Output path for export (optional)")
    parser.add_argument("-v", "--verbose", action="store_true", help="Enable verbose output")
    parser.add_argument("-s", "--silent", action="store_true", help="Suppress non-essential output")
    
    args = parser.parse_args()
    
    # Process command line arguments
    verbose = args.verbose
    silent = args.silent
    
    if args.import_path:
        import_json_to_sqlite(args.import_path, args.db, verbose, silent)
    elif args.export_path:
        export_sqlite_to_json(args.export_path, args.output, verbose, silent)
    else:
        # Default paths
        json_path = str(Path(__file__).parent / "data" / "sample_memories.json")
        db_path = str(Path(__file__).parent / "data" / "memory.db")
        
        # Import data
        if verbose and not silent:
            print(f"Using default paths: JSON={json_path}, DB={db_path}")
        
        import_json_to_sqlite(json_path, db_path, verbose, silent)
