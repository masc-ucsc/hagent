import json
import os
import numpy as np
from pathlib import Path
from typing import List, Dict, Any, Optional
from hagent.tool.memory.db_memory_store import SQLiteMemoryStore

try:
    from sentence_transformers import SentenceTransformer
    HAVE_SENTENCE_TRANSFORMERS = True
except ImportError:
    HAVE_SENTENCE_TRANSFORMERS = False
    print("Warning: sentence-transformers not installed. Embedding creation will be disabled.")

def import_json_to_sqlite(json_path: str, db_path: str = None, verbose: bool = False, 
                         silent: bool = False, create_embeddings: bool = True, force_embeddings: bool = False):
    """
    Import memory data from JSON file to SQLite database.
    
    Args:
        json_path: Path to the JSON file
        db_path: Path to the SQLite database (optional)
        verbose: Whether to print verbose output
        silent: Whether to suppress non-essential output
        create_embeddings: Whether to create embeddings for items without them
        force_embeddings: Whether to force recreation of all embeddings
    """
    # Print debug information about embedding creation
    if not silent:
        if create_embeddings:
            if force_embeddings:
                print("Will force recreation of all embeddings")
            else:
                print("Will create embeddings for items that need them")
        else:
            print("Embedding creation is disabled")
            
    # Check for sentence-transformers before continuing
    if create_embeddings and not HAVE_SENTENCE_TRANSFORMERS:
        if not silent:
            print("Cannot create embeddings: sentence-transformers not installed.")
            print("To enable embeddings, run: pip install sentence-transformers")
    
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
    
    # Initialize sentence transformer for embedding creation if needed
    embedding_model = None
    if create_embeddings and HAVE_SENTENCE_TRANSFORMERS:
        try:
            embedding_model = SentenceTransformer('all-MiniLM-L6-v2')
            if verbose and not silent:
                print("Initialized SentenceTransformer model for embedding creation")
        except Exception as e:
            if verbose and not silent:
                print(f"Error initializing SentenceTransformer: {e}")
            embedding_model = None
    
    # Prepare embeddings storage
    embedding_texts = []
    need_embedding_indices = []
    
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
        
        # Add embedding fields if missing
        if "embedding_text" not in memory or not memory["embedding_text"]:
            # Create embedding text from content, context, and code
            bug_category = memory.get("bug_category", "")
            if not bug_category and "tags" in memory:
                bug_category = " ".join(memory["tags"][:2])
                
            content = memory.get("content", "")
            context = memory.get("context", "")
            code_sample = memory.get("faulty_code", "")[:200]  # First 200 chars
            
            embedding_text = f"{bug_category} {content} {context} {code_sample}"
            memory["embedding_text"] = embedding_text
        
        # Store embedding text for batch processing 
        if embedding_model and (
            force_embeddings or 
            "embedding_index" not in memory or 
            memory["embedding_index"] == -1
        ):
            embedding_texts.append(memory["embedding_text"])
            need_embedding_indices.append(i)
        
        # Add memory to database
        memory_id = db_store.add_memory(memory)
        
        if verbose and not silent and (i == 0 or i == len(memories) - 1 or i % 10 == 0):
            print(f"Imported memory {i+1}/{len(memories)}: {memory.get('content', '')[:50]}...")
    
    # Create and save embeddings if needed
    if embedding_model and embedding_texts:
        try:
            embeddings_dir = Path(db_store.db_path).parent
            embeddings_file = embeddings_dir / "code_embeddings.npy"
            
            if verbose and not silent:
                print(f"Creating embeddings for {len(embedding_texts)} memories...")
                
            # Generate embeddings
            embedding_vectors = embedding_model.encode(embedding_texts)
            
            # Update memory indices and database
            for idx, mem_idx in enumerate(need_embedding_indices):
                memories[mem_idx]["embedding_index"] = idx
                db_store.update_memory(
                    memories[mem_idx]["id"], 
                    {"embedding_index": idx}
                )
            
            # Save embeddings
            np.save(str(embeddings_file), embedding_vectors)
            
            if not silent:
                print(f"✅ CREATED EMBEDDINGS: Saved {len(embedding_vectors)} embeddings to {embeddings_file}")
                print(f"   This file will be used for semantic search")
        except Exception as e:
            if not silent:
                print(f"❌ ERROR creating embeddings: {e}")
    elif embedding_model and not embedding_texts and not silent:
        print("ℹ️ No memories needed new embeddings")
    elif not embedding_model and create_embeddings and not silent:
        print("⚠️ No embeddings created: SentenceTransformer model could not be initialized")
    
    if not silent:
        print(f"Imported {len(memories)} memories to {db_store.db_path}")
        print(f"Note: Extended fields for semantic search are now available")
    
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
    parser.add_argument("--no-embeddings", action="store_true", help="Skip embedding creation")
    parser.add_argument("--force-embeddings", action="store_true", help="Force recreation of embeddings")
    
    args = parser.parse_args()
    
    # Process command line arguments
    verbose = args.verbose
    silent = args.silent
    
    # Determine embedding creation settings
    create_embeddings = not args.no_embeddings
    
    if args.import_path:
        import_json_to_sqlite(args.import_path, args.db, verbose, silent, create_embeddings, args.force_embeddings)
    elif args.export_path:
        export_sqlite_to_json(args.export_path, args.output, verbose, silent)
    else:
        # Default paths
        json_path = str(Path(__file__).parent / "data" / "sample_memories.json")
        db_path = str(Path(__file__).parent / "data" / "memory.db")
        
        # Import data
        if verbose and not silent:
            print(f"Using default paths: JSON={json_path}, DB={db_path}")
        
        import_json_to_sqlite(json_path, db_path, verbose, silent, create_embeddings, args.force_embeddings)
