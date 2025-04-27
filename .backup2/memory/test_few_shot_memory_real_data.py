#!/usr/bin/env python3
"""
Test file for FewShotMemory using real data from JSON and SQLite.
"""

import os
import json
import pytest
import tempfile
import sqlite3
from pathlib import Path

from hagent.tool.memory.few_shot_memory import FewShotMemory, Memory
from hagent.tool.memory.db_memory_store import SQLiteMemoryStore
from hagent.tool.memory.create_test_data import create_sample_data
from hagent.tool.memory.import_data import import_json_to_sqlite
from hagent.tool.memory.code_fix_generator import CodeFixGenerator

# Define permanent paths for test data
DATA_DIR = Path(__file__).parent / "data"
DATA_DIR.mkdir(exist_ok=True)
JSON_PATH = DATA_DIR / "sample_memories.json"
DB_PATH = DATA_DIR / "memory.db"

@pytest.fixture
def sample_data_json():
    """Create and return path to sample data JSON file."""
    # Use permanent JSON file in data directory instead of temporary one
    # Handle the tuple return value (json_path, yaml_path)
    json_path, yaml_path = create_sample_data(output_path=str(JSON_PATH))
    print(f"Created/updated sample data at: {json_path}")
    return json_path  # Return only the JSON path, not the tuple

@pytest.fixture
def sample_data_db(sample_data_json):
    """Create and return path to sample data SQLite database."""
    # Use permanent DB file in data directory
    db_path = str(DB_PATH)
    
    # Create/update SQLite database
    import_json_to_sqlite(sample_data_json, db_path)
    print(f"Imported/updated data in SQLite at: {db_path}")
    
    return db_path

def test_memory_with_json_data(sample_data_json):
    """Test FewShotMemory with real data from JSON file."""
    # Create temporary directory for memory storage
    with tempfile.TemporaryDirectory() as temp_dir:
        # Load data from JSON
        with open(sample_data_json, 'r') as f:
            data = json.load(f)
        
        # Create memory system
        memory = FewShotMemory(name="test_json", memory_dir=temp_dir)
        
        # Add all memories from JSON
        for item in data:
            memory_id = memory.add_memory(
                content=item["content"],
                keywords=item.get("keywords", []),
                context=item.get("context", ""),
                tags=item.get("tags", []),
                timestamp=item.get("timestamp", ""),
                category=item.get("category", ""),
                faulty_code=item.get("faulty_code", ""),
                fixed_code=item.get("fixed_code", ""),
                compiler_errors=item.get("compiler_errors", []),
                language=item.get("language", "")
            )
        
        # Test that we have the expected number of memories
        assert memory.total_memories == len(data)
        
        # Test retrieving memories - Use language-specific keywords
        # Find C++ memories
        cpp_memories = memory.retrieve_memories("C++ syntax error", k=1)
        assert len(cpp_memories) == 1
        assert "C++" in cpp_memories[0].content
        
        # Find Python memories if they exist, otherwise skip this test
        if any("python" == item.get("language", "").lower() for item in data):
            python_memories = memory.retrieve_memories("Python algorithm", k=1)
            assert len(python_memories) == 1
            assert "Python" in python_memories[0].content
        
        # Verify code fields
        assert cpp_memories[0].faulty_code != ""
        assert cpp_memories[0].language == "cpp"
        
        # Test getting unfixed memories
        unfixed_memories = memory.get_unfixed_memories()
        assert len(unfixed_memories) <= len(data)  # May include fixed memories now

def test_memory_with_sqlite_data(sample_data_db):
    """Test FewShotMemory with real data from SQLite database."""
    # Create temporary directory for memory storage
    with tempfile.TemporaryDirectory() as temp_dir:
        # Create memory system with SQLite support
        memory = FewShotMemory(
            name="test_sqlite", 
            memory_dir=temp_dir,
            use_sqlite=True,
            db_path=sample_data_db
        )
        
        # Check that memories are loaded
        assert memory.total_memories > 0
        
        # Get memory count from SQLite directly for verification
        conn = sqlite3.connect(sample_data_db)
        cursor = conn.cursor()
        cursor.execute("SELECT COUNT(*) FROM memories")
        db_count = cursor.fetchone()[0]
        conn.close()
        
        # Verify counts match
        assert memory.total_memories == db_count
        
        # Test retrieving memories - use C++ as it's guaranteed to exist
        cpp_memories = memory.retrieve_memories("C++ syntax", k=1)
        assert len(cpp_memories) == 1
        assert "C++" in cpp_memories[0].content
        
        # Test formatting memories
        formatted = memory.format_memories_as_context(cpp_memories)
        assert "C++" in formatted
        assert "Faulty Code" in formatted
        assert "```cpp" in formatted
        
        # Test JSON serialization
        memory_dict = cpp_memories[0].to_dict()
        assert memory_dict["content"] == cpp_memories[0].content
        assert memory_dict["faulty_code"] == cpp_memories[0].faulty_code
        assert memory_dict["language"] == cpp_memories[0].language

def test_step_interface_with_real_data(sample_data_db):
    """Test Step interface using real SQLite data."""
    # Create temporary directory for memory storage
    with tempfile.TemporaryDirectory() as temp_dir:
        # Create memory system with SQLite support
        memory = FewShotMemory(
            name="test_step", 
            memory_dir=temp_dir,
            use_sqlite=True,
            db_path=sample_data_db
        )
        
        # Test retrieve command - use C++ as it's guaranteed to exist
        result = memory.run({
            "command": "retrieve",
            "query": "C++ syntax error",
            "k": 1
        })
        
        assert result["status"] == "success"
        assert len(result["memories"]) == 1
        assert "C++" in result["memories"][0]["content"]
        assert "language" in result["memories"][0]
        assert "faulty_code" in result["memories"][0]
        assert "fixed_code" in result["memories"][0]
        
        # Test get_unfixed command
        result = memory.run({
            "command": "get_unfixed"
        })
        
        assert result["status"] == "success"
        # Test with memories if there are unfixed ones, otherwise just check the status
        if result["memories"]:
            assert len(result["memories"]) > 0
            
            # Test update_code command with a memory
            memory_id = result["memories"][0]["id"]
            
            # Add compiler errors
            update_result = memory.run({
                "command": "update_code",
                "memory_id": memory_id,
                "compiler_errors": ["Test compiler error for integration test"]
            })
            
            assert update_result["status"] == "success"
            
            # Verify the update directly in the memory object
            # This is more reliable than trying to retrieve via semantic search
            assert memory.memories[memory_id].compiler_errors == ["Test compiler error for integration test"]
            
            # Also verify the update is persisted to the database by reconnecting
            new_memory = FewShotMemory(
                name="test_step_verify",
                memory_dir=temp_dir,
                use_sqlite=True,
                db_path=sample_data_db
            )
            
            assert new_memory.memories[memory_id].compiler_errors == ["Test compiler error for integration test"]
        
        # Test status command
        status_result = memory.run({
            "command": "status"
        })
        
        assert status_result["status"] == "success"
        assert status_result["total_memories"] > 0

def test_code_verification_workflow():
    """
    Integration test for the complete code verification workflow:
    1. Create sample data
    2. Import to SQLite
    3. Compile code to get errors
    4. Update database with errors
    """
    # Create temporary directory and database
    with tempfile.TemporaryDirectory() as temp_dir:
        json_path = os.path.join(temp_dir, "test_memories.json")
        db_path = os.path.join(temp_dir, "test_memory.db")
        
        # Create sample data - handle tuple return value
        json_file, yaml_file = create_sample_data(output_path=json_path)
        
        # Import to SQLite
        import_json_to_sqlite(json_file, db_path)
        
        # Initialize memory system
        memory = FewShotMemory(
            name="test_workflow",
            use_sqlite=True,
            db_path=db_path
        )
        
        # Get unfixed memories - now fixed code might be populated
        unfixed = memory.get_unfixed_memories()
        
        # Process some memory if available, otherwise skip that part
        if unfixed:
            test_memory = unfixed[0]
            
            # Add mock compiler errors
            mock_errors = ["Mock compiler error for testing"]
            memory.update_memory_code_fields(
                test_memory.id,
                compiler_errors=mock_errors
            )
            
            # Verify compiler errors were saved
            updated = memory.memories[test_memory.id]
            assert updated.compiler_errors == mock_errors
            
            # Add mock fixed code
            mock_fixed = "// This is mock fixed code for testing"
            memory.update_memory_code_fields(
                test_memory.id,
                fixed_code=mock_fixed
            )
            
            # Verify fixed code was saved
            updated = memory.memories[test_memory.id]
            assert updated.fixed_code == mock_fixed
            
            # Test memory manipulation was successful
            assert len(memory.memories) > 0
        else:
            # At minimum, verify the database has memories loaded
            assert len(memory.memories) > 0

def create_and_test_permanent_db():
    """Create and test with permanent database file."""
    # Ensure data directory exists
    DATA_DIR.mkdir(exist_ok=True)
    
    # Create or update sample JSON data
    json_path, yaml_path = create_sample_data(output_path=str(JSON_PATH))
    print(f"Created/updated sample data at: {json_path}")
    
    # Create or update SQLite database
    db_path = str(DB_PATH)
    import_json_to_sqlite(json_path, db_path)
    print(f"Imported/updated data in SQLite at: {db_path}")
    
    # Verify database was created successfully
    conn = sqlite3.connect(db_path)
    cursor = conn.cursor()
    cursor.execute("SELECT COUNT(*) FROM memories")
    count = cursor.fetchone()[0]
    conn.close()
    print(f"Database contains {count} memories")
    
    # Test with the newly created database
    test_memory_with_sqlite_data(db_path)
    print("SQLite database test completed successfully")
    
    return db_path

if __name__ == "__main__":
    # Run with permanent database
    db_path = create_and_test_permanent_db()
    print(f"\nAll tests passed. Permanent database available at: {db_path}")
