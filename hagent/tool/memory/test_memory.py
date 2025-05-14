# hagent/tool/memory/test_memory.py

"""
Test program that demonstrates the simplified Memory system with the core add/find functionality.
"""

from pathlib import Path
import tempfile
import os
import uuid
import numpy as np
import pickle
import time

from hagent.tool.memory.few_shot_memory_layer import Memory, MemoryItem
from hagent.tool.compile import Diagnostic
from ruamel.yaml import YAML

def test_memory_add_find():
    """Test the basic add and find functionality of the Memory class."""
    
    # Create a dedicated test database in data directory
    data_dir = Path("data")
    data_dir.mkdir(exist_ok=True)
    
    # Use more descriptive name with unique ID for test database
    test_id = uuid.uuid4().hex[:8]
    db_path = str(data_dir / f"test_code_fix_memory_{test_id}.yaml")
    
    # Initialize Memory system
    memory = Memory(db_path=db_path)
    
    # Create some test diagnostics
    diag1 = Diagnostic("Missing semicolon at line 10")
    diag1.loc = 10
    diag1.file = "test.cpp"
    
    diag2 = Diagnostic("Undefined variable 'foo' at line 15")
    diag2.loc = 15
    diag2.file = "test.cpp"
    
    # Add test entries
    memory.add(
        err=diag1, 
        fix_question="int x = 10\nfoo(x);", 
        fix_answer="int x = 10;\nfoo(x);"
    )
    
    memory.add(
        err=diag2, 
        fix_question="int bar = foo + 5;", 
        fix_answer="int foo = 0;\nint bar = foo + 5;"
    )
    
    # Test finding by exact match
    results = memory.find(diag1, "int x = 10\nfoo(x);")
    print(f"Found {len(results)} exact matches for missing semicolon")
    assert len(results) == 1, "Should find exactly one match"
    assert results[0].fix_answer == "int x = 10;\nfoo(x);", "Should return the correct fix"
    assert results[0].confidence == 1.0, "Exact match should have confidence 1.0"
    
    # Verify embedding was attached to the result
    assert results[0].embedding is not None, "Embedding should be attached to result"
    assert isinstance(results[0].embedding, np.ndarray), "Embedding should be a numpy array"
    
    # Test finding by semantic similarity
    results = memory.find(diag2, "int result = foo + 10;")
    print(f"Found {len(results)} similar matches for undefined variable")
    if results:
        print(f"Best match confidence: {results[0].confidence:.2f}")
        assert results[0].error_type == "Undefined variable 'foo' at line 15", "Should match error type"
    
    # Test no matches
    diag3 = Diagnostic("Type mismatch at line 20")
    diag3.loc = 20
    diag3.file = "test.cpp"
    results = memory.find(diag3, "string s = 42;")
    assert len(results) == 0, "Should find no matches for unknown error type"
    
    # Compute expected embeddings path based on the naming convention
    embeddings_path = str(Path(db_path).with_stem(f"{Path(db_path).stem}_embeddings")) + ".pkl"
    
    # Ensure the database and embeddings files were created
    assert os.path.exists(db_path), "Database file should exist"
    assert os.path.getsize(db_path) > 0, "Database file should not be empty"
    assert os.path.exists(embeddings_path), "Embeddings file should exist"
    assert os.path.getsize(embeddings_path) > 0, "Embeddings file should not be empty"
    
    # Verify embeddings are stored in both YAML and pickle
    # Check YAML file contains embeddings
    yaml = YAML(typ='safe')
    with open(db_path, 'r') as f:
        yaml_data = yaml.load(f)
    
    assert len(yaml_data) == 2, "YAML file should contain 2 memory items"
    assert "embedding" in yaml_data[0], "YAML entries should contain embeddings"
    assert yaml_data[0]["embedding"] is not None, "Embeddings should not be None in YAML"
    
    # Check pickle file contains embeddings
    with open(embeddings_path, 'rb') as f:
        pickle_data = pickle.load(f)
    
    assert len(pickle_data) == 2, "Pickle file should contain 2 embeddings"
    for memory_id, embedding in pickle_data.items():
        assert isinstance(embedding, np.ndarray), "Embeddings in pickle should be numpy arrays"
    
    print(f"Memory add/find test passed! Test database saved at {db_path}")
    
    # Test reopening the database to ensure persistence
    memory2 = Memory(db_path=db_path)
    
    # Verify embeddings were loaded from both sources
    assert len(memory2.embeddings) == 2, "Should have loaded 2 embeddings"
    
    # Verify embeddings were properly attached to memory items
    for memory_item in memory2.memories.values():
        assert memory_item.embedding is not None, "Memory items should have embeddings attached"
    
    # Test finding loads the embeddings correctly
    results = memory2.find(diag1, "int x = 10\nfoo(x);")
    assert len(results) == 1, "Should find the persisted entry after reopening"
    assert results[0].embedding is not None, "Embedding should be loaded from storage"
    print(f"Successfully verified database and embeddings persistence at {db_path}")

def test_memory_embeddings_dual_storage():
    """Test that embeddings persist in both YAML and pickle formats."""
    
    # Use a descriptive path for this test
    data_dir = Path("data")
    data_dir.mkdir(exist_ok=True)
    timestamp = int(time.time())
    db_path = str(data_dir / f"dual_storage_memory_test_{timestamp}.yaml")
    
    # Create a unique diagnostic for this test run
    unique_msg = f"Test diagnostic {uuid.uuid4().hex[:8]}"
    diag = Diagnostic(unique_msg)
    diag.loc = 1
    diag.file = "test.cpp"
    
    # First instance: add data
    memory1 = Memory(db_path=db_path)
    memory1.add(
        err=diag,
        fix_question="// Test question",
        fix_answer="// Test answer"
    )
    
    # Expected embeddings path
    embeddings_path = str(Path(db_path).with_stem(f"{Path(db_path).stem}_embeddings")) + ".pkl"
    
    # Check that both storage files were created
    assert os.path.exists(db_path), "YAML file should exist"
    assert os.path.exists(embeddings_path), "Pickle file should exist"
    
    # Store the number of embeddings
    embedding_count = len(memory1.embeddings)
    
    # Second instance: verify data and embeddings were persisted in both formats
    memory2 = Memory(db_path=db_path)
    
    # Verify embeddings were loaded
    assert len(memory2.embeddings) == embedding_count, f"Should have loaded {embedding_count} embeddings"
    
    # Verify items have embeddings attached
    for memory_id, memory_item in memory2.memories.items():
        assert memory_item.embedding is not None, "Memory items should have embeddings attached"
        assert memory_id in memory2.embeddings, "Embeddings dictionary should contain all memory IDs"
        # Verify the embeddings in the item match those in the dictionary
        assert np.array_equal(memory_item.embedding, memory2.embeddings[memory_id]), "Embeddings should match"
    
    # Find the entry
    results = memory2.find(diag, "// Test question")
    
    if results:
        print(f"Found persisted entry with unique ID {unique_msg}")
        assert results[0].fix_answer == "// Test answer", "Answer should match what was stored"
        assert results[0].embedding is not None, "Embedding should be loaded from storage"
        print("Memory embeddings dual storage test passed!")
    else:
        print(f"WARNING: Could not find persisted entry for {unique_msg}")
    
    # Add a new item and verify both storage mechanisms are updated
    new_diag = Diagnostic(f"New test {uuid.uuid4().hex[:8]}")
    new_diag.loc = 2
    new_diag.file = "test.cpp"
    
    memory2.add(
        err=new_diag,
        fix_question="// New question",
        fix_answer="// New answer"
    )
    
    # Verify the embeddings count has increased
    assert len(memory2.embeddings) == embedding_count + 1, "Embeddings count should have increased"
    
    # Verify both storage files have been updated with the new item
    # Check YAML
    yaml = YAML(typ='safe')
    with open(db_path, 'r') as f:
        yaml_data = yaml.load(f)
    assert len(yaml_data) == embedding_count + 1, "YAML should contain the new item"
    
    # Check pickle
    with open(embeddings_path, 'rb') as f:
        pickle_data = pickle.load(f)
    assert len(pickle_data) == embedding_count + 1, "Pickle should contain the new embedding"
    
    # Third instance: verify all data persisted in both formats
    memory3 = Memory(db_path=db_path)
    assert len(memory3.embeddings) == embedding_count + 1, "Should load all embeddings"
    assert len(memory3.memories) == embedding_count + 1, "Should load all memory items"
    
    # Verify all items have embeddings
    for memory_item in memory3.memories.values():
        assert memory_item.embedding is not None, "All memory items should have embeddings"
    
    print(f"Successfully verified dual storage persistence at {db_path} and {embeddings_path}")
    
if __name__ == "__main__":
    test_memory_add_find()
    test_memory_embeddings_dual_storage()