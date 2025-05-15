# hagent/tool/memory/utils.py

import re
import numpy as np
from typing import List, Dict, Union, Optional
from sentence_transformers import SentenceTransformer
from pathlib import Path
import json
import os
from dataclasses import dataclass
from datetime import datetime
from ruamel.yaml import YAML
from hagent.tool.compile import Diagnostic

# Initialize SentenceTransformer model (this will be reused)
sentence_model = SentenceTransformer('all-MiniLM-L6-v2')

def normalize_code(code: str) -> str:
    """Normalize code for better comparison by removing extra whitespace and comments"""
    # Determine language based on content to handle language-specific comments
    language = "generic"
    if "module" in code and ("endmodule" in code or "wire" in code or "reg" in code):
        language = "verilog"
    elif "entity" in code and "architecture" in code:
        language = "vhdl"
    elif "circuit" in code and ("module" in code or "io" in code) and "extends" in code:
        language = "chisel"
    
    # Remove language-specific comments
    if language == "verilog":
        # Remove Verilog/SystemVerilog style comments
        code = re.sub(r'//.*?\n', '\n', code)
        code = re.sub(r'/\*.*?\*/', '', code, flags=re.DOTALL)
    elif language == "vhdl":
        # Remove VHDL style comments
        code = re.sub(r'--.*?\n', '\n', code)
    elif language == "chisel":
        # Remove Scala/Chisel style comments
        code = re.sub(r'//.*?\n', '\n', code)
        code = re.sub(r'/\*.*?\*/', '', code, flags=re.DOTALL)
    else:
        # Default: Remove C++ style comments
        code = re.sub(r'//.*?\n', '\n', code)
        code = re.sub(r'/\*.*?\*/', '', code, flags=re.DOTALL)
    
    # Remove blank lines and leading/trailing whitespace
    lines = [line.strip() for line in code.splitlines() if line.strip()]
    
    # Remove whitespace between tokens while preserving tokens
    normalized_lines = []
    for line in lines:
        # Keep important whitespace (between words/identifiers) but normalize it
        normalized_line = re.sub(r'\s+', ' ', line)
        normalized_lines.append(normalized_line)
    
    return '\n'.join(normalized_lines)

def calculate_metrics(prediction: str, reference: str) -> Dict[str, float]:
    """Calculate basic metrics comparing prediction to reference."""
    # Handle empty or None values
    if not prediction or not reference:
        return {
            "exact_match": 0,
            "code_token_overlap": 0.0
        }
    
    # Convert to strings if they're not already
    prediction = str(prediction).strip()
    reference = str(reference).strip()
    
    # Calculate exact match using normalized code
    pred_normalized = normalize_code(prediction)
    ref_normalized = normalize_code(reference)
    exact_match = int(pred_normalized == ref_normalized)
    
    # Tokenize the normalized code
    pred_tokens = set(re.findall(r'[a-zA-Z_][a-zA-Z0-9_]*|\d+|\S', pred_normalized))
    ref_tokens = set(re.findall(r'[a-zA-Z_][a-zA-Z0-9_]*|\d+|\S', ref_normalized))
    
    # Calculate token overlap (Jaccard similarity)
    if not pred_tokens or not ref_tokens:
        code_token_overlap = 0.0
    else:
        intersection = len(pred_tokens.intersection(ref_tokens))
        union = len(pred_tokens.union(ref_tokens))
        code_token_overlap = intersection / union if union > 0 else 0.0
    
    # Return simplified metrics
    metrics = {
        "exact_match": exact_match,
        "code_token_overlap": code_token_overlap
    }
    
    return metrics

def save_results(results: Dict, output_path: str):
    """Save evaluation results to a file (JSON or YAML)."""
    path = Path(output_path)
    suffix = path.suffix.lower()
    
    # Create directory if it doesn't exist
    path.parent.mkdir(parents=True, exist_ok=True)
    
    if suffix == '.json':
        with open(output_path, 'w') as f:
            json.dump(results, f, indent=2)
    elif suffix in ['.yaml', '.yml']:
        yaml = YAML()
        yaml.indent(mapping=2, sequence=4, offset=2)
        with open(output_path, 'w') as f:
            yaml.dump(results, f)
    else:
        print(f"Unrecognized file extension '{suffix}'. Defaulting to JSON format.")
        with open(output_path, 'w') as f:
            json.dump(results, f, indent=2)
            
    # print(f"Results saved to {output_path}")

@dataclass
class CppBugExample:
    """A single example of a C++ bug from the sample_memories dataset"""
    id: str
    content: str
    keywords: List[str]
    context: str
    tags: List[str]
    timestamp: str
    category: str
    faulty_code: str
    fix_answer: str
    compiler_errors: List[str]
    language: str
    line_number: Optional[int]
    error_type: str
    bug_category: str
    embedding_text: str
    embedding_index: int
    
    @property
    def fixed_code(self):
        """Alias for fix_answer for backward compatibility"""
        return self.fix_answer

def load_cpp_bugs_dataset(file_path: Union[str, Path]) -> List[CppBugExample]:
    """
    Load the C++ bugs dataset from a JSON or YAML file.
    
    Args:
        file_path: Path to the file containing the dataset
        
    Returns:
        List of CppBugExample objects containing the parsed data
    """
    if isinstance(file_path, str):
        file_path = Path(file_path)
        
    if not file_path.exists():
        raise FileNotFoundError(f"Dataset file not found at {file_path}")
    
    # Load data based on file extension
    suffix = file_path.suffix.lower()
    
    if suffix == '.json':
        with open(file_path, 'r', encoding='utf-8') as f:
            data = json.load(f)
    elif suffix in ['.yaml', '.yml']:
        yaml = YAML(typ='safe')
        with open(file_path, 'r', encoding='utf-8') as f:
            data = yaml.load(f)
    else:
        raise ValueError(f"Unsupported file format: {suffix}. Expected .json, .yaml, or .yml")
    
    samples = []
    
    for bug_idx, bug in enumerate(data):
        try:
            # Handle both fix_answer and fixed_code (legacy) format
            fix_answer = bug.get("fix_answer")
            if fix_answer is None:
                fix_answer = bug.get("fixed_code", "")  # Fall back to fixed_code if fix_answer is not present
                
            sample = CppBugExample(
                id=bug["id"],
                content=bug["content"],
                keywords=bug["keywords"],
                context=bug["context"],
                tags=bug["tags"],
                timestamp=bug["timestamp"],
                category=bug["category"],
                faulty_code=bug["faulty_code"],
                fix_answer=fix_answer,
                compiler_errors=bug["compiler_errors"],
                language=bug["language"],
                line_number=bug.get("line_number"),
                error_type=bug["error_type"],
                bug_category=bug["bug_category"],
                embedding_text=bug["embedding_text"],
                embedding_index=bug["embedding_index"]
            )
            samples.append(sample)
            
        except Exception as e:
            print(f"Error processing bug example {bug_idx}:")
            print(str(e))
            raise e
    
    # Print statistics
    # print(f"\nLoaded {len(samples)} C++ bug examples from {file_path}")
    error_types = {}
    for sample in samples:
        if sample.error_type in error_types:
            error_types[sample.error_type] += 1
        else:
            error_types[sample.error_type] = 1
    
    # print("\nError type distribution:")
    for error_type, count in error_types.items():
        print(f"  {error_type}: {count}")
    
    return samples

def create_diagnostic_from_errors(error_msgs: List[str], file_path: Optional[str] = "", line_number: Optional[int] = 0) -> Diagnostic:
    """
    Create a Diagnostic object from a list of error messages
    
    Args:
        error_msgs: List of error messages
        file_path: Path to the file with the error
        line_number: Line number where the error occurred
        
    Returns:
        A Diagnostic object representing the error
    """
    if not error_msgs:
        # Create an empty diagnostic if no errors
        return Diagnostic("")
    
    # Use the first error message as the main message
    diag = Diagnostic(error_msgs[0])
    
    # Set additional fields
    diag.file = file_path
    
    # If line number wasn't extracted from the error message, use the provided one
    if hasattr(diag, 'loc') and diag.loc <= 0 and line_number > 0:
        diag.loc = line_number
    
    # Add any additional error messages as hints
    if len(error_msgs) > 1:
        diag.hint = "\n".join(error_msgs[1:])
    
    return diag
