import json
import os
import uuid
import datetime
from pathlib import Path

def read_buggy_code(file_path):
    """Read buggy code from a file."""
    try:
        with open(file_path, 'r') as f:
            return f.read()
    except Exception as e:
        print(f"Error reading file {file_path}: {str(e)}")
        return ""

def create_sample_data(output_path=None):
    """
    Create sample memory data by reading buggy code files.
    Fixed code is initially empty and will be filled by the code fixing system.
    
    Args:
        output_path: Optional path for output JSON file. If not provided, 
                     will save to default location.
    
    Returns:
        Path to the created JSON file.
    """
    # Define paths to buggy code files
    base_path = Path(__file__).parent
    verilog_path = base_path / "buggy_verilog" / "buggy_counter.v"
    cpp_path = base_path / "buggy_cpp" / "buggy_linked_list.cpp"
    python_path = base_path / "buggy_python" / "buggy_sorting.py"
    
    # Current timestamp
    current_time = datetime.datetime.now()
    timestamp = current_time.strftime("%Y%m%d%H%M")
    iso_timestamp = current_time.isoformat()
    
    # Create sample data with buggy code but empty fixed code
    sample_data = [
        {
            "id": str(uuid.uuid4()),
            "content": "Fix the reset logic in this Verilog counter module.",
            "keywords": ["Verilog", "counter", "reset", "bug", "hardware"],
            "context": "Debugging Verilog modules",
            "tags": ["verilog", "hardware", "debugging"],
            "timestamp": timestamp,
            "category": "Verilog",
            "faulty_code": read_buggy_code(verilog_path),
            "fixed_code": "",  # Empty initially, will be filled by code fixer
            "compiler_errors": [],  # Will store compiler diagnostic messages
            "language": "verilog",
            "created_at": iso_timestamp
        },
        {
            "id": str(uuid.uuid4()),
            "content": "Fix memory management issues in this C++ array implementation.",
            "keywords": ["C++", "memory leak", "array", "bug", "destructor"],
            "context": "C++ memory management",
            "tags": ["cpp", "memory management", "debugging"],
            "timestamp": timestamp,
            "category": "C++",
            "faulty_code": read_buggy_code(cpp_path),
            "fixed_code": "",  # Empty initially, will be filled by code fixer
            "compiler_errors": [],  # Will store compiler diagnostic messages
            "language": "cpp",
            "created_at": iso_timestamp
        },
        {
            "id": str(uuid.uuid4()),
            "content": "Fix the sorting algorithm implementation bugs in Python.",
            "keywords": ["Python", "sorting", "algorithm", "bug", "bubble sort"],
            "context": "Python algorithm debugging",
            "tags": ["python", "algorithms", "debugging"],
            "timestamp": timestamp,
            "category": "Python",
            "faulty_code": read_buggy_code(python_path),
            "fixed_code": "",  # Empty initially, will be filled by code fixer
            "compiler_errors": [],  # Will store compiler diagnostic messages
            "language": "python",
            "created_at": iso_timestamp
        }
    ]
    
    # Determine output path
    if output_path is None:
        # Use default path
        data_dir = Path(__file__).parent / "data"
        data_dir.mkdir(exist_ok=True)
        file_path = data_dir / "sample_memories.json"
    else:
        # Use provided path
        file_path = Path(output_path)
        file_path.parent.mkdir(exist_ok=True)
    
    # Write to JSON file
    with open(file_path, "w") as f:
        json.dump(sample_data, f, indent=2)
    
    print(f"Created sample data at: {file_path}")
    return str(file_path)

if __name__ == "__main__":
    create_sample_data()
