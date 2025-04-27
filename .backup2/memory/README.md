# Few-Shot Memory System

A comprehensive code storage, retrieval, and fixing system that leverages past examples to guide future solutions.

## Overview

The Few-Shot Memory system provides a semantic memory layer for storing, retrieving, and fixing code examples. It includes:

- Memory storage in both SQLite database and JSON/YAML formats
- Semantic search for finding similar code examples
- Automated code fixing using compiler diagnostics and LLM integration
- Support for multiple programming languages (C++, Python, Verilog)
- Token usage and cost tracking for optimization

## Directory Structure

```
hagent/tool/memory/
├── __init__.py                        # Package initialization
├── code_fix_generator.py              # Code fixing system
├── code_fix_llm_config.yaml           # LLM configuration for code fixing
├── create_test_data.py                # Test data generation
├── db_memory_store.py                 # SQLite database interface
├── few_shot_memory.py                 # Main memory system implementation
├── few_shot_memory_conf.yaml          # Memory system configuration
├── import_data.py                     # Data import/export utilities
├── programs/                          # Example code pairs (buggy/fixed)
│   ├── 1_missing_semicolon_*.cpp      # Example 1: Missing semicolon
│   ├── 2_undeclared_variable_*.cpp    # Example 2: Undeclared variable
│   ├── 3_mismatched_brackets_*.cpp    # Example 3: Mismatched brackets
│   ├── ...                            # Additional examples
├── README.md                          # This file
├── run                                # Convenience script for tests
├── test_few_shot_memory.py            # Unit tests
└── test_few_shot_memory_real_data.py  # Integration tests
```

## Components

### Core Files

- **`few_shot_memory.py`**: The main memory system with semantic retrieval capabilities
- **`db_memory_store.py`**: SQLite database backend for persistent memory storage
- **`code_fix_generator.py`**: Automated code fixing tool that uses compiler messages and LLMs
- **`import_data.py`**: Utilities for importing/exporting between JSON and SQLite
- **`create_test_data.py`**: Creates sample buggy code data from the programs directory

### Example Programs

The `programs` directory contains paired examples of buggy code and their fixed versions:

1. **Syntax Errors**:
   - Missing semicolons (`1_missing_semicolon_*.cpp`)
   - Mismatched brackets (`3_mismatched_brackets_*.cpp`)
   - Uninitialized variables (`10_uninitialized_variable_*.cpp`)

2. **Variable Issues**:
   - Undeclared variables (`2_undeclared_variable_*.cpp`)
   - Variable shadowing (`9_variable_shadowing_*.cpp`)

3. **Memory Management**:
   - Null pointer dereference (`5_null_pointer_*.cpp`)
   - Memory leaks (`7_memory_leak_*.cpp`)

4. **Other Error Types**:
   - Infinite loops (`4_infinite_loop_*.cpp`)
   - Array bounds issues (`6_array_bounds_*.cpp`)
   - Division by zero (`8_division_by_zero_*.cpp`)

## Usage

### Prerequisites

Make sure you have the required Python packages installed:

```bash
poetry install
```

Required Python packages include:
- sentence-transformers (for embeddings)
- sqlite3 (for database operations)
- ruamel.yaml (for YAML file handling)

### Step 1: Creating Test Data

Generate sample data from the code pairs in the `programs` directory:

```bash
# Basic usage
poetry run python hagent/tool/memory/create_test_data.py

# With verbose output and silent mode
poetry run python hagent/tool/memory/create_test_data.py -v -s

# Specify custom output location
poetry run python hagent/tool/memory/create_test_data.py --output /path/to/custom_memories.json
```

This will:
1. Read all buggy/fixed code pairs from the `programs` directory
2. Generate compiler errors by attempting to compile the buggy code
3. Create a structured JSON and YAML file with all the examples
4. Store these files in the `data` directory by default

### Step 2: Importing Data to SQLite

Import the generated JSON data into the SQLite database:

```bash
# Basic usage (uses default paths)
poetry run python hagent/tool/memory/import_data.py

# Specify input JSON and database path
poetry run python hagent/tool/memory/import_data.py --import /path/to/memories.json --db /path/to/database.db

# With verbose output
poetry run python hagent/tool/memory/import_data.py -v
```

You can also export data from the database back to JSON:

```bash
poetry run python hagent/tool/memory/import_data.py --export /path/to/database.db --output /path/to/output.json
```

### Step 3: Running the Code Fix Generator

The code fix generator automatically fixes buggy code examples in the database:

```bash
# Basic usage
poetry run python hagent/tool/memory/code_fix_generator.py

# Filter by programming language
poetry run python hagent/tool/memory/code_fix_generator.py --language cpp

# Use custom database and LLM configuration
poetry run python hagent/tool/memory/code_fix_generator.py --db-path /path/to/memory.db --llm-config /path/to/config.yaml

# Create a sample LLM configuration file
poetry run python hagent/tool/memory/code_fix_generator.py --create-config

# Enable debug mode for detailed logs
poetry run python hagent/tool/memory/code_fix_generator.py --debug
```

#### LLM Configuration

Code fixing uses LLMs when available. Set up your API keys:

```bash
# Choose at least one based on which LLM you want to use
export OPENAI_API_KEY=your_key_here
export ANTHROPIC_API_KEY=your_key_here
export FIREWORKS_AI_API_KEY=your_key_here
```

You can also create or customize the LLM configuration:

```bash
poetry run python hagent/tool/memory/code_fix_generator.py --create-config
```

This will generate a `code_fix_llm_config.yaml` file that you can modify.

### Working with the Database

View and query the database content:

```bash
sqlite3 hagent/tool/memory/data/memory.db
```

Common SQLite commands:
```sql
.mode column
.headers on
.tables                                  -- List all tables
SELECT * FROM memories LIMIT 5;          -- View first 5 memories
SELECT id, language, faulty_code FROM memories WHERE language = 'cpp';  -- Filter by language
SELECT * FROM memories WHERE fixed_code = '';  -- Find unfixed examples
.schema memories                         -- View table schema
.quit                                    -- Exit
```

Export to CSV:
```bash
sqlite3 hagent/tool/memory/data/memory.db ".headers on" ".mode csv" ".output memories.csv" "SELECT * FROM memories;" ".quit"
```

## Programming with the Memory System

### Adding Memories

```python
from hagent.tool.memory.few_shot_memory import FewShotMemory

# Initialize with SQLite storage
memory = FewShotMemory(use_sqlite=True)

# Add a new memory
memory_id = memory.add_memory(
    content="Fix the sorting algorithm implementation bugs",
    faulty_code="def bubble_sort(arr):\n    # Buggy code here",
    language="python",
    keywords=["sorting", "algorithm", "bug"],
    tags=["python", "algorithms"]
)
```

### Retrieving Memories

```python
# Get similar examples using semantic search
similar_memories = memory.retrieve_memories("python sort algorithm error", k=3)

# Format for use in an LLM prompt
context = memory.format_memories_as_context(similar_memories)

# Get all unfixed examples of a specific language
unfixed_python = memory.get_unfixed_memories(language="python")
```

### Updating Memories with Fixes

```python
# Update compiler errors
memory.update_memory_code_fields(
    memory_id=memory_id,
    compiler_errors=["Error: IndexError in line 5"]
)

# Update fixed code
memory.update_memory_code_fields(
    memory_id=memory_id,
    fixed_code="def bubble_sort(arr):\n    # Fixed code"
)
```

### Using the Step Interface

The memory system implements the HAgent Step interface:

```python
result = memory.run({
    "command": "retrieve",
    "query": "python sort algorithm",
    "k": 3
})

result = memory.run({
    "command": "add",
    "content": "Fix the division by zero error",
    "faulty_code": "def divide(a, b):\n    return a/b",
    "language": "python"
})

result = memory.run({
    "command": "update_code",
    "memory_id": memory_id,
    "fixed_code": "def divide(a, b):\n    if b == 0:\n        return None\n    return a/b"
})
```

## Testing

Run the unit tests:

```bash
poetry run python -m pytest hagent/tool/memory/test_few_shot_memory.py -v
```

Run the integration tests with real data:

```bash
poetry run python -m pytest hagent/tool/memory/test_few_shot_memory_real_data.py -v
```

Or use the convenience script:

```bash
hagent/tool/memory/run
```

## End-to-End Example Workflow

Here's a complete workflow example:

```bash
# 1. Create sample data from the provided code examples
poetry run python hagent/tool/memory/create_test_data.py

# 2. Import the data into SQLite
poetry run python hagent/tool/memory/import_data.py

# 3. Run the code fix generator to automatically fix the code
poetry run python hagent/tool/memory/code_fix_generator.py

# 4. View the results in the database
sqlite3 hagent/tool/memory/data/memory.db "SELECT id, language, substr(faulty_code, 1, 30), substr(fixed_code, 1, 30) FROM memories;"
```

## Extending the System

### Adding New Languages

1. Create a new compiler interface class in `code_fix_generator.py`:
   ```python
   class NewLanguageCompiler(CompilerInterface):
       def compile(self, code: str) -> List[str]:
           # Implement compilation and error extraction
           return ["Error messages"]
   ```

2. Register the compiler in the `CodeFixGenerator` constructor:
   ```python
   self.compilers = {
       "newlang": NewLanguageCompiler(),
       # existing compilers...
   }
   ```

3. Add language detection in `create_test_data.py`

### Adding Custom Error Analysis

You can modify the error analysis in `get_compiler_errors` in `create_test_data.py` to handle specific error patterns for your language.
