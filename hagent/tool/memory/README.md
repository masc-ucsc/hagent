# Few-Shot Memory System

A comprehensive code storage, retrieval, and fixing system that leverages past examples to guide future solutions.

## Overview

The Few-Shot Memory system provides a semantic memory layer for storing, retrieving, and fixing code examples. It includes:

- Memory storage in both SQLite database and JSON formats
- Semantic search for finding similar code examples
- Automated code fixing using compiler diagnostics and LLM integration
- Support for multiple programming languages (Verilog, C++, Python)
- Token usage and cost tracking for optimization

## Components

### Core Files

- **`few_shot_memory.py`**: The main memory system with semantic retrieval capabilities
- **`db_memory_store.py`**: SQLite database backend for persistent memory storage
- **`code_fix_generator.py`**: Automated code fixing tool that uses compiler messages and LLMs
- **`import_data.py`**: Utilities for importing/exporting between JSON and SQLite
- **`create_test_data.py`**: Creates sample buggy code data for demonstration and testing

### Data Directories

- **`buggy_cpp/`**: Example buggy C++ code samples
- **`buggy_python/`**: Example buggy Python code samples
- **`buggy_verilog/`**: Example buggy Verilog code samples
- **`data/`**: Storage for database and JSON files
- **`memories/`**: Storage for embedding vectors and retriever state

### Test Files

- **`test_few_shot_memory.py`**: Unit tests for the memory system
- **`test_few_shot_memory_real_data.py`**: Integration tests using real data

## Usage

### Creating Test Data

Generate sample buggy code examples:

```bash
poetry run python hagent/tool/memory/create_test_data.py -v -s
```

### Importing Data to SQLite

Import the JSON data into the SQLite database:

```bash
poetry run python hagent/tool/memory/import_data.py -v -s
```

### Running the Code Fix Generator

Automatically fix code examples in the database:

```bash
poetry run python hagent/tool/memory/code_fix_generator.py
```

Options:
- `--db-path`: Specify a custom database path
- `--llm-config`: Specify a custom LLM configuration file
- `--language`: Filter by programming language
- `--create-config`: Create a sample LLM configuration file
- `--debug`: Enable detailed debug output

### Working with the Database

View the database content:

```bash
sqlite3 hagent/tool/memory/data/memory.db
.mode column
.headers on
.tables                   # List all tables
SELECT * FROM memories;   # View all memories
.schema memories          # View table schema
.quit                     # Exit
```

Export to CSV:

```bash
sqlite3 hagent/tool/memory/data/memory.db ".headers on" ".mode csv" ".output memories.csv" "SELECT * FROM memories;" ".quit"
```

## Memory System API

### Adding Memories

```python
from hagent.tool.memory.few_shot_memory import FewShotMemory

memory = FewShotMemory(use_sqlite=True)
memory_id = memory.add_memory(
    content="Fix the sorting algorithm implementation bugs",
    faulty_code="def bubble_sort(arr):\n    # Buggy code here",
    language="python",
    keywords=["sorting", "algorithm", "bug"]
)
```

### Retrieving Memories

```python
# Get similar examples
similar_memories = memory.retrieve_memories("python sort algorithm error", k=3)

# Format for use in an LLM prompt
context = memory.format_memories_as_context(similar_memories)
```

### Updating Memories with Fixes

```python
memory.update_memory_code_fields(
    memory_id=memory_id,
    compiler_errors=["Error: IndexError in line 5"],
    fixed_code="def bubble_sort(arr):\n    # Fixed code"
)
```

## Code Fix Generator

The code fix generator performs a multi-stage fixing process:

1. Compile the faulty code and collect errors
2. Generate initial fix using LLM or built-in rules
3. Verify the fix by compiling again
4. Apply a second round of fixes if needed
5. Update the database with the fixed code and compiler errors

## Database Schema

The system uses a SQLite database with the following tables:

- **`memories`**: Stores memory content, code, and metadata
- **`keywords`**: Links memories to keywords (many-to-many)
- **`tags`**: Links memories to tags (many-to-many)
- **`links`**: Creates connections between related memories

## Example Workflow

1. Create test data with buggy code examples:
   ```bash
   poetry run python hagent/tool/memory/create_test_data.py
   ```

2. Import data to SQLite:
   ```bash
   poetry run python hagent/tool/memory/import_data.py
   ```

3. Run the code fix generator to fix errors:
   ```bash
   poetry run python hagent/tool/memory/code_fix_generator.py
   ```

4. View the results in the database:
   ```bash
   sqlite3 hagent/tool/memory/data/memory.db "SELECT id, language, substr(faulty_code, 1, 30), substr(fixed_code, 1, 30) FROM memories;"
   ```

## Contributing

To add support for new languages:

1. Create a new compiler interface class in `code_fix_generator.py`
2. Add language-specific error detection and fixing routines
3. Update the compiler mappings in the `CodeFixGenerator` class
