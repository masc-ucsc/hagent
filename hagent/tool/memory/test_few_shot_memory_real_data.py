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

# Define permanent paths for test data
DATA_DIR = Path(__file__).parent / "data"
DATA_DIR.mkdir(exist_ok=True)
JSON_PATH = DATA_DIR / "sample_memories.json"
DB_PATH = DATA_DIR / "memory.db"

@pytest.fixture
def sample_data_json():
    """Create and return path to sample data JSON file."""
    # Use permanent JSON file in data directory instead of temporary one
    json_path = str(create_sample_data(output_path=str(JSON_PATH)))
    print(f"Created/updated sample data at: {json_path}")
    return json_path

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
                language=item.get("language", "")
            )
        
        # Test that we have the expected number of memories
        assert memory.total_memories == len(data)
        
        # Test retrieving memories
        verilog_memories = memory.retrieve_memories("Verilog counter", k=1)
        assert len(verilog_memories) == 1
        assert "Verilog" in verilog_memories[0].content
        
        cpp_memories = memory.retrieve_memories("C++ memory management", k=1)
        assert len(cpp_memories) == 1
        assert "C++" in cpp_memories[0].content
        
        # Verify code fields
        assert verilog_memories[0].faulty_code != ""
        assert verilog_memories[0].language == "verilog"

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
        
        # Test retrieving memories
        verilog_memories = memory.retrieve_memories("Verilog counter", k=1)
        assert len(verilog_memories) == 1
        assert "Verilog" in verilog_memories[0].content
        
        # Test formatting memories
        formatted = memory.format_memories_as_context(verilog_memories)
        assert "Verilog" in formatted
        assert "Faulty Code" in formatted
        assert "Fixed Code" in formatted
        assert "```verilog" in formatted
        
        # Test JSON serialization
        memory_dict = verilog_memories[0].to_dict()
        assert memory_dict["content"] == verilog_memories[0].content
        assert memory_dict["faulty_code"] == verilog_memories[0].faulty_code
        assert memory_dict["language"] == verilog_memories[0].language

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
        
        # Test retrieve command
        result = memory.run({
            "command": "retrieve",
            "query": "Python sorting algorithm",
            "k": 1
        })
        
        assert result["status"] == "success"
        assert len(result["memories"]) == 1
        assert "Python" in result["memories"][0]["content"]
        assert "language" in result["memories"][0]
        assert "faulty_code" in result["memories"][0]
        assert "fixed_code" in result["memories"][0]
        
        # Test status command
        status_result = memory.run({
            "command": "status"
        })
        
        assert status_result["status"] == "success"
        assert status_result["total_memories"] > 0

def create_and_test_permanent_db():
    """Create and test with permanent database file."""
    # Ensure data directory exists
    DATA_DIR.mkdir(exist_ok=True)
    
    # Create or update sample JSON data
    json_path = create_sample_data(output_path=str(JSON_PATH))
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
