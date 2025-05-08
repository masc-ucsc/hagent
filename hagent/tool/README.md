# HAgent Tool Library

This directory contains various tools for code analysis, repair, and automation.

## Components

### React System (react.py)

React implements a Reasoning-Acting loop for iterative error fixing. It works by:
1. Checking code for errors
2. Adding diagnostic comments at error locations
3. Generating fixes
4. Repeating until the code is error-free or max iterations reached

React can learn from successful fixes by storing them in a database for future use.

### Memory Layer (memory/few_shot_memory_layer.py)

The memory layer provides semantic search capabilities for code examples:
1. Stores bug/fix pairs with error information
2. Uses embeddings to find similar examples
3. Provides detailed metadata about bugs and fixes
4. Supports multiple programming languages

### ReactMemory Integration (react_memory.py)

ReactMemory combines React's iterative approach with FewShotMemory's semantic search:
1. Uses semantically similar code examples to guide fixes
2. Leverages neural embeddings to find relevant examples
3. Learns from successful fixes as semantic memories
4. Supports the same iterative workflow as React

## Usage Examples

See the test files for usage examples:
- `tests/test_react_compile_gcc_simple.py` - Using React with GCC
- `tests/test_react_compile_slang_simple.py` - Using React with Slang (Verilog)
- `tests/test_react_memory.py` - Using ReactMemory with C++

## Getting Started

```python
from hagent.tool.react_memory import ReactMemory

# Initialize and setup ReactMemory
react_memory = ReactMemory()
react_memory.setup(
    db_path="path/to/memories.yaml",
    learn=True,
    comment_prefix="//"  # Language-specific comment prefix
)

# Use the react_cycle method with appropriate callbacks
fixed_code = react_memory.react_cycle(
    initial_text=buggy_code,
    check_callback=your_check_function,
    fix_callback=your_fix_function
)
```