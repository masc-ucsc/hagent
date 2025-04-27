#!/usr/bin/env python3
"""
Test file for FewShotMemory.
"""

import os
import sys
import tempfile
import unittest
from pathlib import Path

from hagent.tool.memory.few_shot_memory import FewShotMemory, Memory

class TestFewShotMemory(unittest.TestCase):
    """Test class for FewShotMemory."""
    
    def setUp(self):
        """Set up test environment."""
        # Create a temporary directory for memories
        self.test_dir = tempfile.TemporaryDirectory()
        self.memory_dir = self.test_dir.name
        
        # Initialize memory system with the temporary directory
        self.memory = FewShotMemory(
            name="test_memory",
            memory_dir=self.memory_dir
        )
    
    def tearDown(self):
        """Clean up test environment."""
        self.test_dir.cleanup()
    
    def test_add_retrieve_memory(self):
        """Test adding and retrieving memories."""
        # Add test memories
        memory1_id = self.memory.add_memory(
            "Python is a high-level programming language known for its readability and simplicity.",
            keywords=["Python", "programming", "language", "readability"],
            context="Programming languages overview",
            tags=["programming", "language", "python"]
        )
        
        memory2_id = self.memory.add_memory(
            "C++ is a powerful programming language used for system development and performance-critical applications.",
            keywords=["C++", "programming", "performance", "system"],
            context="Programming languages overview",
            tags=["programming", "language", "C++"]
        )
        
        # Verify memories were added
        self.assertEqual(self.memory.total_memories, 2)
        self.assertIn(memory1_id, self.memory.memories)
        self.assertIn(memory2_id, self.memory.memories)
        
        # Test retrieval
        memories = self.memory.retrieve_memories("Python programming language", k=1)
        self.assertEqual(len(memories), 1)
        self.assertEqual(memories[0].id, memory1_id)
        
        memories = self.memory.retrieve_memories("C++ system programming", k=1)
        self.assertEqual(len(memories), 1)
        self.assertEqual(memories[0].id, memory2_id)
    
    def test_format_memories(self):
        """Test formatting memories as context."""
        # Add a test memory
        memory_id = self.memory.add_memory(
            "The quick brown fox jumps over the lazy dog.",
            keywords=["fox", "dog", "jump"],
            context="Animal actions",
            tags=["animals", "action"]
        )
        
        # Retrieve and format
        memories = self.memory.retrieve_memories("fox and dog", k=1)
        formatted = self.memory.format_memories_as_context(memories)
        
        # Check formatting
        self.assertIn("The quick brown fox jumps over the lazy dog", formatted)
        self.assertIn("Animal actions", formatted)
        self.assertIn("fox, dog, jump", formatted)
        self.assertIn("animals, action", formatted)
    
    def test_code_features(self):
        """Test code-specific memory features."""
        # Add a memory with code
        verilog_memory_id = self.memory.add_memory(
            "Fix the reset logic in this Verilog counter module.",
            keywords=["Verilog", "counter", "reset", "bug"],
            context="Debugging Verilog modules",
            tags=["verilog", "hardware", "debugging"],
            faulty_code="""
module buggy_counter(
    input clk,
    input reset_n,
    output reg [3:0] count,
    output overflow
);
    always @(negedge clk) begin
        // Missing reset logic
        if (count == 4'b1111) begin
            count <= 0;
            overflow = 1;
        end else begin
            count <= count + 1;
            overflow = 0;
        end
    end
endmodule
            """,
            compiler_errors=[
                "Error: Non-blocking assignment expected for reg 'overflow'",
                "Error: Missing reset logic"
            ],
            fixed_code="""
module fixed_counter(
    input clk,
    input reset_n,
    output reg [3:0] count,
    output reg overflow
);
    always @(posedge clk) begin
        if (!reset_n) begin
            count <= 0;
            overflow <= 0;
        end else if (count == 4'b1111) begin
            count <= 0;
            overflow <= 1;
        end else begin
            count <= count + 1;
            overflow <= 0;
        end
    end
endmodule
            """,
            language="verilog"
        )
        
        # Verify memory was added
        self.assertEqual(self.memory.total_memories, 1)
        self.assertIn(verilog_memory_id, self.memory.memories)
        
        # Test code-specific retrieval
        memories = self.memory.retrieve_memories("Verilog reset bug", k=1)
        self.assertEqual(len(memories), 1)
        self.assertEqual(memories[0].id, verilog_memory_id)
        
        # Test code-inclusive formatting
        formatted = self.memory.format_memories_as_context(memories, include_code=True)
        self.assertIn("buggy_counter", formatted)
        self.assertIn("Faulty Code", formatted)
        self.assertIn("Compiler Errors", formatted)
        self.assertIn("1. Error: Non-blocking", formatted)
        self.assertIn("Fixed Code", formatted)
        self.assertIn("```verilog", formatted)
        
        # Test code-exclusive formatting
        formatted_no_code = self.memory.format_memories_as_context(memories, include_code=False)
        self.assertNotIn("```verilog", formatted_no_code)
        self.assertNotIn("Faulty Code", formatted_no_code)
    
    def test_update_code_fields(self):
        """Test updating code-related fields."""
        # Add a memory with faulty code only
        memory_id = self.memory.add_memory(
            "Test updating code fields",
            faulty_code="def buggy_function():\n    retrun 'misspelled'",
            language="python"
        )
        
        # Update with compiler errors
        compiler_errors = ["SyntaxError: invalid syntax, did you mean 'return'?"]
        self.memory.update_memory_code_fields(memory_id, compiler_errors=compiler_errors)
        
        # Verify errors were added
        self.assertEqual(self.memory.memories[memory_id].compiler_errors, compiler_errors)
        
        # Update with fixed code
        fixed_code = "def fixed_function():\n    return 'corrected'"
        self.memory.update_memory_code_fields(memory_id, fixed_code=fixed_code)
        
        # Verify code was updated
        self.assertEqual(self.memory.memories[memory_id].fixed_code, fixed_code)
        
        # Verify errors remain unchanged
        self.assertEqual(self.memory.memories[memory_id].compiler_errors, compiler_errors)
    
    def test_get_unfixed_memories(self):
        """Test getting unfixed memories."""
        # Add a memory with fixed code
        fixed_id = self.memory.add_memory(
            "Fixed memory",
            faulty_code="int main() { printf('Hello'); }",
            fixed_code="int main() { printf('Hello'); return 0; }",
            language="cpp"
        )
        
        # Add a memory without fixed code
        unfixed_id = self.memory.add_memory(
            "Unfixed memory",
            faulty_code="int main() { prinft('Typo'); }",
            language="cpp"
        )
        
        # Add another unfixed memory with different language
        unfixed_python_id = self.memory.add_memory(
            "Unfixed Python memory",
            faulty_code="print 'Python 2 syntax'",
            language="python"
        )
        
        # Get all unfixed memories
        unfixed = self.memory.get_unfixed_memories()
        self.assertEqual(len(unfixed), 2)
        self.assertIn(unfixed_id, [m.id for m in unfixed])
        self.assertIn(unfixed_python_id, [m.id for m in unfixed])
        
        # Get unfixed memories filtered by language
        cpp_unfixed = self.memory.get_unfixed_memories(language="cpp")
        self.assertEqual(len(cpp_unfixed), 1)
        self.assertEqual(cpp_unfixed[0].id, unfixed_id)
    
    def test_delete_memory(self):
        """Test deleting a memory."""
        # Add a test memory
        memory_id = self.memory.add_memory("Test memory to delete")
        
        # Verify it was added
        self.assertEqual(self.memory.total_memories, 1)
        self.assertIn(memory_id, self.memory.memories)
        
        # Delete it
        result = self.memory.delete_memory(memory_id)
        
        # Verify it was deleted
        self.assertTrue(result)
        self.assertEqual(self.memory.total_memories, 0)
        self.assertNotIn(memory_id, self.memory.memories)
    
    def test_persistence(self):
        """Test persistence of memories."""
        # Add test memories
        memory_id = self.memory.add_memory(
            "Test persistent memory with code",
            faulty_code="def buggy_function(x):\n    return x+1  # Bug: doesn't handle zero",
            compiler_errors=["Logic error: Function doesn't handle zero correctly"],
            fixed_code="def fixed_function(x):\n    if x == 0:\n        return 0\n    return x+1",
            language="python"
        )
        
        # Create a new memory instance (should load existing memories)
        new_memory = FewShotMemory(
            name="test_memory",
            memory_dir=self.memory_dir
        )
        
        # Verify memories were loaded
        self.assertEqual(new_memory.total_memories, 1)
        self.assertIn(memory_id, new_memory.memories)
        self.assertEqual(new_memory.memories[memory_id].language, "python")
        self.assertIn("buggy_function", new_memory.memories[memory_id].faulty_code)
        self.assertEqual(len(new_memory.memories[memory_id].compiler_errors), 1)
    
    def test_step_interface(self):
        """Test Step interface implementation."""
        # Test add command with code
        add_data = {
            "command": "add",
            "content": "Fix sorting direction in bubble sort implementation",
            "keywords": ["sorting", "algorithm", "bug"],
            "tags": ["python", "algorithms"],
            "faulty_code": "def bubble_sort(arr):\n    for i in range(len(arr)-1):\n        for j in range(len(arr)-1):\n            if arr[j] < arr[j+1]:  # Bug: sorts in descending order\n                arr[j], arr[j+1] = arr[j+1], arr[j]\n    return arr",
            "fixed_code": "",
            "compiler_errors": [],
            "language": "python"
        }
        result = self.memory.run(add_data)
        self.assertEqual(result["status"], "success")
        memory_id = result["memory_id"]
        
        # Test update_code command
        update_data = {
            "command": "update_code",
            "memory_id": memory_id,
            "compiler_errors": ["IndexError: Loop may access arr[j+1] out of bounds", 
                               "Logic error: Comparison direction creates descending order"]
        }
        result = self.memory.run(update_data)
        self.assertEqual(result["status"], "success")
        
        # Test get_unfixed command
        unfixed_data = {
            "command": "get_unfixed",
            "language": "python"
        }
        result = self.memory.run(unfixed_data)
        self.assertEqual(result["status"], "success")
        self.assertEqual(len(result["memories"]), 1)
        self.assertEqual(result["memories"][0]["id"], memory_id)
        
        # Now add a fix
        update_fix_data = {
            "command": "update_code",
            "memory_id": memory_id,
            "fixed_code": "def bubble_sort(arr):\n    for i in range(len(arr)):\n        for j in range(len(arr)-i-1):\n            if arr[j] > arr[j+1]:  # Fixed: sorts in ascending order\n                arr[j], arr[j+1] = arr[j+1], arr[j]\n    return arr"
        }
        result = self.memory.run(update_fix_data)
        self.assertEqual(result["status"], "success")
        
        # Test get_unfixed again - should be empty
        result = self.memory.run(unfixed_data)
        self.assertEqual(result["status"], "success")
        self.assertEqual(len(result["memories"]), 0)
        
        # Test retrieve command
        retrieve_data = {
            "command": "retrieve",
            "query": "sorting algorithm python",
            "k": 1
        }
        result = self.memory.run(retrieve_data)
        self.assertEqual(result["status"], "success")
        self.assertEqual(len(result["memories"]), 1)
        self.assertEqual(result["memories"][0]["id"], memory_id)
        self.assertIn("faulty_code", result["memories"][0])
        self.assertIn("fixed_code", result["memories"][0])
        self.assertEqual(result["memories"][0]["language"], "python")
        
        # Test status command
        status_data = {
            "command": "status"
        }
        result = self.memory.run(status_data)
        self.assertEqual(result["status"], "success")
        self.assertEqual(result["total_memories"], 1)
        
        # Test delete command
        delete_data = {
            "command": "delete",
            "memory_id": memory_id
        }
        result = self.memory.run(delete_data)
        self.assertEqual(result["status"], "success")

if __name__ == "__main__":
    unittest.main()
