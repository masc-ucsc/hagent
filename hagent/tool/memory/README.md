## C++ Bug Detection System 🐛

This repository includes a specialized implementation focused on C++ bug detection and fixing using our memory approach. The system uses a few-shot memory mechanism to identify similar bugs in a database and suggest fixes based on past examples.

### Components:

- **few_shot_memory_layer.py**: Core memory system that handles:
  - Storing and retrieving C++ bug examples
  - Embedding-based similarity search using SentenceTransformer
  - Database management in both YAML and JSON formats
  - Memory caching for performance optimization

- **utils.py**: Utility functions including:
  - Code normalization for better comparison
  - Metrics calculation for evaluating fixes
  - Dataset loading and processing
  - C++ bug example representation

- **test_few_shot_memory.py**: Test program that:
  - Loads or creates a memory database of C++ bugs
  - Accepts a C++ file with a potential bug
  - Searches for similar bugs in the memory system
  - Suggests fixes based on similar examples
  - Outputs results in YAML format

- **run**: Bash script to:
  - Run tests on multiple pre-defined buggy C++ programs
  - Track exact matches vs similar examples
  - Generate summary statistics

### How It Works 🛠️

1. The system loads C++ bug examples into memory
2. Each example includes buggy code, fixed code, error type, and other metadata
3. When given a new C++ file with a potential bug:
   - The system first looks for an exact match after normalizing the code
   - If no exact match is found, it uses semantic similarity via embeddings
   - The most similar examples are returned with their fixes
4. Results are saved to YAML files for further analysis

## Getting Started 🚀

1. Run the C++ bug detection system on a single file:
```bash
python test_few_shot_memory.py -p programs/1_missing_semicolon_buggy.cpp
```

2. Or run the batch test script to test all example bugs:
```bash
chmod +x run
./run
```

### Command-line Arguments

For `test_few_shot_memory.py`, the following arguments are available:

- `-p, --program`: Path to the C++ program file to analyze (required)
- `-d, --database`: Path to the memory database file (default: data/sample_memories.yaml)
- `-o, --output`: Path to save the results (default: auto-generated)
- `-b, --backend`: Backend to use (default: openai)
- `-m, --model`: Model to use (default: gpt-4o-mini)

### Example Usage

To analyze a specific C++ file:
```bash
python test_few_shot_memory.py -p your_code.cpp -o results/your_results.yaml
```


