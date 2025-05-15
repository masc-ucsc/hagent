# HAgent Few-Shot Memory System

The memory system provides a mechanism for storing, retrieving, and learning from code examples to help fix programming bugs. It uses both exact matching and semantic similarity to find relevant examples.

## Components

### Core Classes

- **Memory**: Basic memory unit that represents individual bug examples with metadata
  - Stores code, error information, fixes, and metadata
  - Contains utility methods for file handling and error detection

- **FewShotMemory**: Main memory system with embedding-based retrieval
  - Uses SentenceTransformer for semantic similarity search
  - Manages database of bug examples in YAML/JSON formats
  - Implements caching for performance optimization

### Supported Languages

The system can detect and fix bugs in multiple languages:
- C/C++
- Python
- Verilog/SystemVerilog
- VHDL
- Chisel (Scala-based HDL)
- PyRTL
- Spade
- Silice
- and more...

## Usage

### Basic Usage

```python
from hagent.tool.memory import FewShotMemory, Memory
from hagent.tool.compile import Diagnostic

# Initialize memory system with database path
memory_system = FewShotMemory(db_path="path/to/database.yaml")

# Create a diagnostic for an error
diagnostic = Diagnostic("Syntax error: expected ';'")
diagnostic.file = "path/to/file.cpp"
diagnostic.loc = 10  # Line number where error occurred

# Find similar examples
matches = memory_system.find(
    err=diagnostic,
    fix_question="your buggy code here"
)

# Process matches
if matches:
    best_match = matches[0]
    print(f"Found match with confidence: {best_match.confidence:.4f}")
    print(f"Suggested fix: {best_match.fix_answer}")

# Add new example to memory
memory_id = memory_system.add(
    err=diagnostic,
    fix_question="buggy code",
    fix_answer="fixed code"
)
print(f"Added to memory with ID: {memory_id}")
```

### Command-line Tool

You can use the test program to analyze and add bug examples. When using Poetry for dependency management, use the following format:

```bash
# Analyze a C++ file
poetry run python test_few_shot_memory.py -p programs/1_missing_semicolon_buggy.cpp

# Analyze a PyRTL file
poetry run python test_few_shot_memory.py -p programs/12_wire_assignment_buggy.pyrtl

# Analyze a VHDL file
poetry run python test_few_shot_memory.py -p programs/13_signal_declaration_buggy.vhd
```

### Command-line Arguments

For `test_few_shot_memory.py`, the following arguments are available:

- `-p, --program`: Path to the program file to analyze (required)
- `-d, --database`: Path to the memory database file (default: data/test_memory_database.yaml)
- `-o, --output`: Path to save the results (default: auto-generated)

Examples with additional arguments:

```bash
# Specify a custom database path
poetry run python test_few_shot_memory.py -p programs/12_wire_assignment_buggy.pyrtl -d custom_database.yaml

# Specify a custom output file
poetry run python test_few_shot_memory.py -p programs/1_missing_semicolon_buggy.cpp -o results/my_fix.yaml
```

### Batch Testing

Run tests on multiple programs using the provided script:

```bash
# Make the script executable
chmod +x run

# Run the batch test script
./run

# Using poetry
poetry run bash run
```

## How It Works

1. **Database Building**:
   - The system loads or creates a database of bug examples
   - Each example includes buggy code, fixed code, error type, and other metadata

2. **Bug Analysis**:
   - When given new buggy code, the system extracts compiler errors and diagnostics
   - It normalizes the code to improve matching accuracy

3. **Matching Process**:
   - First attempts to find an exact match using normalized code
   - If no exact match is found, uses embeddings for semantic similarity
   - Returns the most similar examples with their fixes and confidence scores

4. **Learning**:
   - New bug examples can be added to the database
   - The system maintains both YAML and JSON versions of the database
   - Embeddings are cached for performance

## Testing

To run the tests for the memory system:

```bash
# Run all tests
poetry run pytest tests/

# Run a specific test file
poetry run pytest test_react_compile_slang_simple.py
```

## Integration with React Tool

The memory system is integrated with the HAgent React tool for iterative error fixing:

```python
from hagent.tool.react import React

# Initialize React with memory system
react = React()
react.setup(db_path="path/to/database.yaml", learn=True)

# Use React for iterative error fixing
fixed_code = react.react_cycle(
    initial_text=buggy_code,
    check_callback=your_checker_function,
    fix_callback=your_fixer_function
)
```

## Advanced Features

- **Code Normalization**: Removes comments and standardizes whitespace for better matching
- **Confidence Scores**: Returned matches include confidence scores based on similarity
- **Embedding Caching**: Embeddings are cached for faster repeated lookups
- **Multiple Database Formats**: Supports both YAML and JSON formats
- **Backward Compatibility**: Maintains compatibility with older database formats


