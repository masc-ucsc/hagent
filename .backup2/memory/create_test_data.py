import json
import os
from ruamel.yaml import YAML
import uuid
import datetime
import subprocess
import tempfile
import re
import sys
from pathlib import Path
from typing import List, Dict, Tuple, Any

def read_code_file(file_path):
    """Read code from a file."""
    try:
        with open(file_path, 'r') as f:
            return f.read()
    except Exception as e:
        print(f"Error reading file {file_path}: {str(e)}")
        return ""

def detect_language(file_path):
    """Detect programming language from file extension."""
    extension = Path(file_path).suffix.lower()
    language_map = {
        '.cpp': 'C++',
        '.cc': 'C++',
        '.c': 'C',
        '.py': 'Python',
        '.v': 'Verilog',
        '.sv': 'SystemVerilog',
        '.js': 'JavaScript',
        '.ts': 'TypeScript',
        '.java': 'Java',
        '.go': 'Go',
        '.rb': 'Ruby',
        '.rs': 'Rust'
    }
    return language_map.get(extension, 'Unknown')

def get_language_code(language):
    """Convert full language name to code."""
    language_codes = {
        'C++': 'cpp',
        'C': 'c',
        'Python': 'python',
        'Verilog': 'verilog',
        'SystemVerilog': 'systemverilog',
        'JavaScript': 'js',
        'TypeScript': 'ts',
        'Java': 'java',
        'Go': 'go',
        'Ruby': 'ruby',
        'Rust': 'rust'
    }
    return language_codes.get(language, language.lower())

def get_compiler_errors(code: str, language: str, file_name: str) -> Tuple[List[str], Dict[str, Any]]:
    """
    Compile the code and return errors and analysis.
    
    Args:
        code: The source code to compile
        language: The programming language
        file_name: Original file name for context
        
    Returns:
        Tuple of (error_messages, analysis_data)
    """
    errors = []
    analysis = {
        'error_type': 'unknown',
        'line_number': None,
        'severity': 'error',
        'description': '',
        'context': '',
        'specific_issue': '',
        'keywords': [],
        'tags': []
    }
    
    if language == 'C++':
        with tempfile.NamedTemporaryFile(suffix='.cpp', delete=False) as tmp:
            tmp_path = tmp.name
            tmp.write(code.encode('utf-8'))
        
        try:
            # Try Clang++ for more detailed error messages
            try:
                result = subprocess.run(['clang++', '-fsyntax-only', '-Wall', '-std=c++17', tmp_path], 
                                      capture_output=True, text=True, timeout=10)
                
                if result.returncode != 0:
                    errors = [line for line in result.stderr.strip().split('\n') if line]
                    
                    # Parse error details
                    if errors:
                        # Extract line number, error type, and message
                        match = re.search(r':(\d+):\d+: (error|warning): (.+)', errors[0])
                        if match:
                            analysis['line_number'] = int(match.group(1))
                            analysis['severity'] = match.group(2)
                            analysis['description'] = match.group(3)
                            
                            # Determine error type
                            if "expected ';'" in analysis['description']:
                                analysis['error_type'] = 'missing_semicolon'
                                analysis['specific_issue'] = 'missing semicolon'
                            elif "use of undeclared identifier" in analysis['description']:
                                analysis['error_type'] = 'undeclared_variable'
                                analysis['specific_issue'] = 'undeclared variable'
                            elif "expected ')'" in analysis['description'] or "expected '}'" in analysis['description']:
                                analysis['error_type'] = 'mismatched_brackets'
                                analysis['specific_issue'] = 'mismatched brackets or parentheses'
                            elif "null pointer" in analysis['description'] or "dereference" in analysis['description']:
                                analysis['error_type'] = 'null_pointer'
                                analysis['specific_issue'] = 'null pointer dereference'
                            elif "array" in analysis['description'] and ("bounds" in analysis['description'] or "initialization" in analysis['description']):
                                analysis['error_type'] = 'array_bounds'
                                analysis['specific_issue'] = 'array bounds or initialization issue'
                            elif "leak" in analysis['description'] or ("new" in analysis['description'] and "delete" in analysis['description']):
                                analysis['error_type'] = 'memory_leak'
                                analysis['specific_issue'] = 'memory leak or allocation issue'
                            elif "division" in analysis['description'] or "operator" in analysis['description']:
                                analysis['error_type'] = 'operator_error'
                                analysis['specific_issue'] = 'incorrect operator usage'
                            elif "shadow" in analysis['description']:
                                analysis['error_type'] = 'variable_shadowing'
                                analysis['specific_issue'] = 'variable shadowing'
                            elif "uninitialized" in analysis['description']:
                                analysis['error_type'] = 'uninitialized_variable'
                                analysis['specific_issue'] = 'uninitialized variable'
                            else:
                                # Extract from filename if can't determine from error
                                match = re.search(r'(\d+)_([a-z_]+)_buggy', file_name)
                                if match:
                                    analysis['error_type'] = match.group(2)
                                    analysis['specific_issue'] = match.group(2).replace('_', ' ')
                    
                    # Get context from code
                    if analysis['line_number']:
                        lines = code.split('\n')
                        if 0 <= analysis['line_number']-1 < len(lines):
                            analysis['context'] = lines[analysis['line_number']-1].strip()
            except (FileNotFoundError, subprocess.TimeoutExpired):
                # Try GCC instead
                try:
                    result = subprocess.run(['g++', '-fsyntax-only', '-Wall', '-std=c++17', tmp_path], 
                                          capture_output=True, text=True, timeout=10)
                    
                    if result.returncode != 0:
                        errors = [line for line in result.stderr.strip().split('\n') if line]
                except (FileNotFoundError, subprocess.TimeoutExpired):
                    # Fallback: basic analysis from code
                    err_msg = "Could not compile code - compiler not available"
                    errors.append(err_msg)
                    analysis['description'] = err_msg
        
        finally:
            if os.path.exists(tmp_path):
                os.remove(tmp_path)
    
    elif language == 'Python':
        with tempfile.NamedTemporaryFile(suffix='.py', delete=False) as tmp:
            tmp_path = tmp.name
            tmp.write(code.encode('utf-8'))
        
        try:
            # Check syntax errors
            result = subprocess.run([sys.executable, '-m', 'py_compile', tmp_path], 
                                  capture_output=True, text=True, timeout=10)
            
            if result.returncode != 0:
                errors = [line for line in result.stderr.strip().split('\n') if line]
                
                # Extract information from Python errors
                if errors:
                    match = re.search(r'File ".*", line (\d+)', errors[0])
                    if match:
                        analysis['line_number'] = int(match.group(1))
                    
                    if "SyntaxError" in errors[-1]:
                        analysis['error_type'] = 'syntax_error'
                        analysis['specific_issue'] = 'syntax error'
                        # Get the specific error message
                        match = re.search(r'SyntaxError: (.+)', errors[-1])
                        if match:
                            analysis['description'] = match.group(1)
        except Exception as e:
            errors.append(f"Error analyzing Python code: {str(e)}")
        finally:
            if os.path.exists(tmp_path):
                os.remove(tmp_path)
    
    elif language == 'Verilog':
        # Similar pattern for Verilog using appropriate tools
        errors.append("Verilog compilation not implemented")
        analysis['description'] = "Verilog error analysis would be done here"
    
    # Generate keywords and tags based on analysis
    base_keywords = [language]
    base_tags = [get_language_code(language), 'debugging']
    
    if analysis['specific_issue']:
        keywords = base_keywords + [analysis['specific_issue'], 'bug', analysis['severity']]
        if 'error_type' in analysis and analysis['error_type'] != 'unknown':
            tags = base_tags + [analysis['error_type'].replace('_', ' ')]
            if any(category in analysis['error_type'] for category in ['pointer', 'memory', 'leak']):
                tags.append('memory management')
            elif any(category in analysis['error_type'] for category in ['syntax', 'semicolon', 'brackets']):
                tags.append('syntax')
            elif any(category in analysis['error_type'] for category in ['variable', 'uninitialized']):
                tags.append('variables')
        else:
            tags = base_tags
    else:
        keywords = base_keywords + ['bug']
        tags = base_tags
    
    analysis['keywords'] = list(set(keywords))
    analysis['tags'] = list(set(tags))
    
    # If no errors found but we expect there to be errors
    if not errors and '_buggy' in file_name:
        generic_error = f"Code contains errors not detected by automatic analysis"
        errors.append(generic_error)
        if not analysis['description']:
            analysis['description'] = generic_error
    
    return errors, analysis

def generate_bug_description(analysis, bug_number, file_name):
    """Generate a human-readable bug description based on error analysis."""
    
    # Try to extract bug type from filename if not in analysis
    if not analysis.get('specific_issue'):
        match = re.search(r'(\d+)_([a-z_]+)_buggy', file_name)
        if match:
            bug_type = match.group(2).replace('_', ' ')
            analysis['specific_issue'] = bug_type
    
    # Generate description based on available information
    if analysis.get('description') and analysis.get('specific_issue'):
        description = f"Fix the {analysis['specific_issue']} in this code. Error: {analysis['description']}"
    elif analysis.get('description'):
        description = f"Fix the code error: {analysis['description']}"
    elif analysis.get('specific_issue'):
        description = f"Fix the {analysis['specific_issue']} in this code."
    else:
        # Fallback
        description = f"Fix the bug in this code (Bug #{bug_number})."
    
    return description

def create_sample_data(output_path=None, output_yaml_path=None):
    """
    Create sample memory data by reading buggy and fixed code files from programs directory.
    
    Args:
        output_path: Optional path for output JSON file. If not provided, 
                     will save to default location.
        output_yaml_path: Optional path for output YAML file.
    
    Returns:
        Tuple of paths to the created JSON and YAML files.
    """
    # Define path to programs directory
    base_path = Path(__file__).parent
    programs_path = base_path / "programs"
    
    # Verify programs directory exists
    if not programs_path.exists():
        print(f"Programs directory not found at {programs_path}")
        return None, None
    
    # Find all buggy/fixed file pairs
    code_pairs = []
    for buggy_file in programs_path.glob("*_buggy.*"):
        # Construct fixed file path with same extension
        fixed_file = buggy_file.parent / buggy_file.name.replace("_buggy", "_fixed")
        
        if fixed_file.exists():
            code_pairs.append((buggy_file, fixed_file))
    
    if not code_pairs:
        print("No buggy/fixed code pairs found")
        return None, None
    
    # Current timestamp
    current_time = datetime.datetime.now()
    timestamp = current_time.strftime("%Y%m%d%H%M")
    iso_timestamp = current_time.isoformat()
    
    # Create sample data with buggy and fixed code
    sample_data = []
    
    for buggy_file, fixed_file in code_pairs:
        # Extract bug number from filename
        filename = buggy_file.name
        match = re.search(r'(\d+)_', filename)
        bug_number = match.group(1) if match else "0"
        
        # Detect language
        language = detect_language(buggy_file)
        language_code = get_language_code(language)
        
        # Read buggy and fixed code
        buggy_code = read_code_file(buggy_file)
        fixed_code = read_code_file(fixed_file)
        
        # Get compiler errors and analysis
        compiler_errors, analysis = get_compiler_errors(buggy_code, language, filename)
        
        # Generate bug description
        description = generate_bug_description(analysis, bug_number, filename)
        
        # Extract context for searching
        context = f"{language} programming bug fix: "
        if analysis.get('specific_issue'):
            context += analysis['specific_issue']
        else:
            # Extract from filename
            match = re.search(r'\d+_([a-z_]+)_buggy', filename)
            if match:
                context += match.group(1).replace('_', ' ')
            else:
                context += "code error"
        
        # Create memory object
        memory = {
            "id": str(uuid.uuid4()),
            "content": f"{language} Bug #{bug_number}: {description}",
            "keywords": analysis['keywords'],
            "context": context,
            "tags": analysis['tags'],
            "timestamp": timestamp,
            "category": language,
            "faulty_code": buggy_code,
            "fixed_code": fixed_code,
            "compiler_errors": compiler_errors,
            "language": language_code,
            "created_at": iso_timestamp,
            "line_number": analysis.get('line_number'),
            "error_type": analysis.get('error_type', 'unknown')
        }
        
        sample_data.append(memory)
    
    # Determine output paths
    if output_path is None:
        # Use default path
        data_dir = Path(__file__).parent / "data"
        data_dir.mkdir(exist_ok=True)
        json_path = data_dir / "sample_memories.json"
    else:
        # Use provided path
        json_path = Path(output_path)
        json_path.parent.mkdir(exist_ok=True)
    
    if output_yaml_path is None:
        yaml_path = json_path.with_suffix('.yaml')
    else:
        yaml_path = Path(output_yaml_path)
        yaml_path.parent.mkdir(exist_ok=True)
    
    # Write to JSON file
    with open(json_path, "w") as f:
        json.dump(sample_data, f, indent=2)
    
    # Write to YAML file using ruamel.yaml
    yaml = YAML()
    yaml.indent(mapping=2, sequence=4, offset=2)  # Set indentation for better readability
    yaml.preserve_quotes = True  # Preserve quotes in strings
    
    with open(yaml_path, "w") as f:
        yaml.dump(sample_data, f)
    
    print(f"Created sample data at: {json_path} and {yaml_path}")
    print(f"Generated {len(sample_data)} memory entries from buggy/fixed code pairs")
    return str(json_path), str(yaml_path)

if __name__ == "__main__":
    create_sample_data()
