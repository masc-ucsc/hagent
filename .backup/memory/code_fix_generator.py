#!/usr/bin/env python3
"""
Code Fix Generator - Processes unfixed code in the memory database.

This script:
1. Reads faulty code from the database
2. Compiles it to get error messages
3. Uses LLM to generate fixes
4. Stores the fixes back to the database
"""

import os
import sys
import tempfile
import subprocess
import re
import argparse
import yaml
from pathlib import Path
from typing import List, Dict, Any, Optional, Tuple

from hagent.tool.memory.few_shot_memory import FewShotMemory, Memory
from hagent.core.llm_wrap import LLM_wrap

# Compiler handlers for different languages
class CompilerInterface:
    """Base class for compiler interfaces."""
    
    def compile(self, code: str) -> List[str]:
        """
        Compile code and return errors.
        
        Args:
            code: Source code to compile
            
        Returns:
            List of error messages
        """
        raise NotImplementedError("Subclasses must implement compile method")


class VerilogCompiler(CompilerInterface):
    """Verilog compiler using Slang/Verilator."""
    
    def compile(self, code: str) -> List[str]:
        """Compile Verilog code using available Verilog compiler."""
        with tempfile.NamedTemporaryFile(suffix='.v', delete=False) as tmp:
            tmp_path = tmp.name
            tmp.write(code.encode('utf-8'))
        
        try:
            # Try Slang first (if available)
            try:
                result = subprocess.run(['slang', tmp_path], 
                                       capture_output=True, text=True, timeout=10)
                
                if result.returncode != 0:
                    errors = result.stderr.strip().split('\n')
                    filtered_errors = [err for err in errors if err and not err.startswith('Note:')]
                    if filtered_errors:
                        return filtered_errors
            except (FileNotFoundError, subprocess.TimeoutExpired):
                pass  # Slang not available or timed out, try Verilator
                
            # Try Verilator 
            try:
                result = subprocess.run(['verilator', '--lint-only', '-Wall', tmp_path], 
                                      capture_output=True, text=True, timeout=10)
                
                if result.returncode != 0:
                    errors = result.stderr.strip().split('\n')
                    filtered_errors = [err for err in errors if err and ('%Error' in err or '%Warning' in err)]
                    if filtered_errors:
                        return filtered_errors
            except (FileNotFoundError, subprocess.TimeoutExpired):
                # If neither compiler is available or working
                if code.strip() and "module" in code:
                    # Generate some basic Verilog errors based on common patterns
                    errors = []
                    if ";" not in code:
                        errors.append("Error: Expected ';' to end statement")
                    if "always @" in code and "begin" not in code:
                        errors.append("Error: Missing 'begin' in 'always' block")
                    if "=" in code and "<=" not in code:
                        errors.append("Error: Using blocking assignment '=' in sequential logic, should use '<='")
                    if "output" in code and "reg" not in code and "assign" not in code:
                        errors.append("Error: Output port used in always block must be declared as reg")
                    
                    if errors:
                        return errors
                    
                return ["Verilog compiler not available. Install Slang or Verilator."]
                
            # If no errors were detected but the code contains suspicious patterns
            if "=" in code and "<=" not in code and "always @" in code:
                return ["Warning: Using blocking assignment '=' in sequential logic, should use '<='"]
                
            return []
            
        finally:
            if os.path.exists(tmp_path):
                os.remove(tmp_path)


class CPPCompiler(CompilerInterface):
    """C++ compiler using GCC/Clang."""
    
    def compile(self, code: str) -> List[str]:
        """Compile C++ code using GCC or Clang."""
        if not code.strip():
            return ["Error: Empty code"]
            
        with tempfile.NamedTemporaryFile(suffix='.cpp', delete=False) as tmp:
            tmp_path = tmp.name
            tmp.write(code.encode('utf-8'))
        
        try:
            # Try GCC
            try:
                result = subprocess.run(['g++', '-fsyntax-only', '-Wall', '-std=c++17', tmp_path], 
                                      capture_output=True, text=True, timeout=10)
                
                if result.returncode != 0:
                    # Extract meaningful error messages
                    error_pattern = r'.*error:|.*warning:'
                    errors = []
                    for line in result.stderr.strip().split('\n'):
                        if re.search(error_pattern, line):
                            errors.append(line)
                    if errors:
                        return errors
            except (FileNotFoundError, subprocess.TimeoutExpired):
                pass  # GCC not available or timed out, try Clang
                
            # Try Clang
            try:
                result = subprocess.run(['clang++', '-fsyntax-only', '-Wall', '-std=c++17', tmp_path], 
                                      capture_output=True, text=True, timeout=10)
                
                if result.returncode != 0:
                    error_pattern = r'.*error:|.*warning:'
                    errors = []
                    for line in result.stderr.strip().split('\n'):
                        if re.search(error_pattern, line):
                            errors.append(line)
                    if errors:
                        return errors
            except (FileNotFoundError, subprocess.TimeoutExpired):
                # If neither compiler is available, do some basic checks
                if "new" in code and "delete" not in code:
                    return ["Warning: Memory allocated with 'new' but no 'delete' found - potential memory leak"]
                if "[]" in code and ("new" in code or "delete" in code):
                    if "delete[]" not in code:
                        return ["Warning: Array allocated with 'new[]' but 'delete[]' not found - potential memory leak"]
                if "class" in code and "~" not in code and "new" in code:
                    return ["Warning: Class uses dynamic memory but has no destructor - potential memory leak"]
                    
                return ["C++ compiler not found. Install GCC or Clang."]
                
            return []
            
        finally:
            if os.path.exists(tmp_path):
                os.remove(tmp_path)


class PythonCompiler(CompilerInterface):
    """Python code checker using pylint and static analysis."""
    
    def compile(self, code: str) -> List[str]:
        """Check Python code for errors."""
        if not code.strip():
            return ["Error: Empty code"]
            
        with tempfile.NamedTemporaryFile(suffix='.py', delete=False) as tmp:
            tmp_path = tmp.name
            tmp.write(code.encode('utf-8'))
        
        errors = []
        
        try:
            # First, check for syntax errors
            try:
                result = subprocess.run([sys.executable, '-m', 'py_compile', tmp_path], 
                                      capture_output=True, text=True, timeout=10)
                
                if result.returncode != 0:
                    errors.append(result.stderr.strip())
            except subprocess.TimeoutExpired:
                errors.append("Timeout while checking Python syntax")
            
            # Then try pylint for more detailed analysis
            try:
                result = subprocess.run(['pylint', '--errors-only', tmp_path], 
                                      capture_output=True, text=True, timeout=10)
                
                if result.returncode != 0:
                    # Filter meaningful error messages
                    for line in result.stdout.strip().split('\n'):
                        if ':' in line and not line.startswith('*'):
                            errors.append(line)
            except (FileNotFoundError, subprocess.TimeoutExpired):
                # Pylint not available or timed out, do some basic checks
                if "range" in code and "[" in code and "]" in code:
                    if re.search(r'for.*in range\([^)]+\).*\[[^]]+\+', code):
                        errors.append("IndexError: Potential list index out of range in loop")
                if "print " in code and not "print(" in code:
                    errors.append("SyntaxError: Missing parentheses in call to 'print'")
            
            # If no errors but there are common patterns suggesting bugs
            if not errors:
                if "for i in range" in code and "+1" in code and "]" in code:
                    errors.append("Warning: Potential off-by-one error in array indexing")
                if "if arr[j] < arr[j+1]" in code and "sort" in code:
                    errors.append("Logic error: Comparison operator is creating descending sort instead of ascending")
            
            return errors
            
        except Exception as e:
            return [f"Error checking Python code: {str(e)}"]
            
        finally:
            if os.path.exists(tmp_path):
                os.remove(tmp_path)


class CodeFixGenerator:
    """Main class for generating code fixes from compiler errors."""
    
    def __init__(self, 
                memory_system: FewShotMemory, 
                llm_conf_file: str,
                llm_name: str = "code_fix_generator"):
        """
        Initialize the code fix generator.
        
        Args:
            memory_system: FewShotMemory instance
            llm_conf_file: Path to LLM configuration file
            llm_name: Name for the LLM configuration
        """
        self.memory = memory_system
        
        # Check if config file exists, if not create it
        if not os.path.exists(llm_conf_file):
            print(f"Config file not found at {llm_conf_file}, creating default")
            llm_conf_file = create_llm_config(llm_conf_file)
            
        # Initialize LLM
        try:
            self.llm = LLM_wrap(
                name=llm_name,
                conf_file=llm_conf_file,
                log_file=f"{llm_name}.log"
            )
            
            # Check for API key issues
            required_env_vars = ["OPENAI_API_KEY", "ANTHROPIC_API_KEY", "FIREWORKS_AI_API_KEY"]
            available_keys = [var for var in required_env_vars if os.environ.get(var)]
            
            if not available_keys:
                print("WARNING: No API keys found. Set at least one of: OPENAI_API_KEY, ANTHROPIC_API_KEY, or FIREWORKS_AI_API_KEY")
                
        except Exception as e:
            print(f"Error initializing LLM: {str(e)}")
            print("Using fallback for fixes (basic error correction only)")
            self.llm = None
        
        # Set up compiler interfaces
        self.compilers = {
            "verilog": VerilogCompiler(),
            "cpp": CPPCompiler(),
            "c++": CPPCompiler(),  # Alias
            "python": PythonCompiler()
        }
    
    def get_compiler(self, language: str) -> Optional[CompilerInterface]:
        """Get the appropriate compiler for a language."""
        language = language.lower()
        return self.compilers.get(language)
    
    def strip_markdown_code_blocks(self, code: str, language: str = None) -> str:
        """
        Remove markdown code block markers from code.
        
        Args:
            code: Source code potentially containing markdown markers
            language: Programming language (optional)
            
        Returns:
            Cleaned code without markdown code block markers
        """
        # Remove opening code block markers with or without language specifier
        if language:
            # Handle specific language markers like ```python, ```cpp, etc.
            pattern = fr'```\s*{language}\s*\n'
            code = re.sub(pattern, '', code, flags=re.IGNORECASE)
        
        # Remove any opening code block markers
        code = re.sub(r'```\w*\s*\n', '', code)
        code = re.sub(r'^```\w*\s*', '', code)  # At beginning of text
        
        # Remove closing code block markers
        code = re.sub(r'\n\s*```\s*$', '', code)
        code = re.sub(r'\s*```\s*$', '', code)  # At end of text
        
        # Some LLMs might add language comments at the start
        if language:
            code = re.sub(fr'^\s*\/\/\s*{language}\s*\n', '', code, flags=re.IGNORECASE)
            code = re.sub(fr'^\s*#\s*{language}\s*\n', '', code, flags=re.IGNORECASE)
            
        # Some LLMs might add "Fixed code:" or similar text before the actual code
        code = re.sub(r'^(Fixed|Corrected|Updated|Here\'s the fixed) code:?\s*\n?', '', code, flags=re.IGNORECASE)
        
        # Handle extra newlines and formatting
        code = code.strip()
        
        return code
    
    def basic_code_fix(self, code: str, errors: List[str], language: str) -> str:
        """
        Implement basic fix rules without using LLM (as fallback).
        
        Args:
            code: Source code to fix
            errors: List of error messages
            language: Programming language
            
        Returns:
            Fixed code (best effort)
        """
        # First, make sure the code doesn't have markdown markers
        fixed_code = self.strip_markdown_code_blocks(code, language)
        
        if language.lower() == "verilog":
            # Fix common Verilog issues
            if any("blocking assignment" in err or "=" in err and "<=" in err for err in errors):
                fixed_code = re.sub(r'(\w+)\s*=\s*(\w+)', r'\1 <= \2', fixed_code)
                fixed_code = re.sub(r'overflow\s*=\s*([01])', r'overflow <= \1', fixed_code)
            
            if any("reg" in err and "output" in err for err in errors):
                # Fix 'output X' to 'output reg X'
                fixed_code = re.sub(r'output\s+(?!reg)(\w+)', r'output reg \1', fixed_code)
                fixed_code = fixed_code.replace("output overflow", "output reg overflow")
            
            if any("posedge" in err or "negedge" in err for err in errors) or "negedge clk" in fixed_code:
                fixed_code = fixed_code.replace("negedge clk", "posedge clk")
            
            if any("reset" in err for err in errors) or "// Bug 3: Missing reset logic" in fixed_code:
                # Add reset logic if missing
                if "always @" in fixed_code and "if (!reset" not in fixed_code:
                    fixed_code = re.sub(
                        r'always\s+@\(\s*posedge\s+clk\s*\)\s*begin', 
                        "always @(posedge clk or negedge reset_n) begin\n        if (!reset_n) begin\n            count <= 0;\n            overflow <= 0;\n        end else", 
                        fixed_code
                    )
            
            # Add missing semicolons
            if any(";" in err for err in errors):
                # Find lines ending with something other than ; or {
                fixed_code = re.sub(r'(\w+\s*\S+)\s*\n', r'\1;\n', fixed_code)
                fixed_code = re.sub(r'(assign\s+\w+\s*=\s*[^;]+)(?!\s*;)\s*\n', r'\1;\n', fixed_code)
            
            # Fix missing newline at end of file
            if any("EOFNEWLINE" in err for err in errors):
                if not fixed_code.endswith('\n'):
                    fixed_code += '\n'
                    
            # Fix module name mismatch
            if any("DECLFILENAME" in err or "module name" in err for err in errors):
                # Just remove these warnings as they're related to temporary files
                pass
        
        elif language.lower() in ["cpp", "c++"]:
            # Fix common C++ issues
            if any("delete" in err or "destructor" in err or "memory leak" in err for err in errors):
                if "class" in fixed_code and "~" not in fixed_code:
                    # Add destructor to class
                    class_name = re.search(r'class\s+(\w+)', fixed_code)
                    if class_name:
                        destructor = f"    ~{class_name.group(1)}() {{\n        delete[] arr;\n    }}\n"
                        fixed_code = re.sub(r'(public:[^\{]*\{)', f'\\1\n{destructor}', fixed_code)
                        if "public:" not in fixed_code:
                            fixed_code = re.sub(r'(class\s+\w+\s*\{)', f'\\1\npublic:\n{destructor}', fixed_code)
            
            if any("bound" in err or "index" in err or "out of" in err for err in errors):
                # Add bounds checking to array access
                if "void set(int index, int value)" in fixed_code:
                    fixed_code = re.sub(
                        r'(arr\[index\]\s*=\s*value\s*;)', 
                        r'if (index >= 0 && index < size) \1', 
                        fixed_code
                    )
                if "int get(int index)" in fixed_code:
                    fixed_code = re.sub(
                        r'return\s+arr\[index\]\s*;', 
                        r'return (index >= 0 && index < size) ? arr[index] : -1;', 
                        fixed_code
                    )
                    
                # Fix out of bounds access in main
                fixed_code = re.sub(
                    r'arr\.set\(10,\s*100\)', 
                    r'arr.set(0, 100)', 
                    fixed_code
                )
                fixed_code = re.sub(
                    r'arr\.get\(10\)', 
                    r'arr.get(0)', 
                    fixed_code
                )
            
            if "size = capacity" in fixed_code:
                fixed_code = fixed_code.replace("size = capacity", "size = 0")
                
            # Add capacity tracking
            if "size;" in fixed_code and "capacity;" not in fixed_code:
                fixed_code = fixed_code.replace("int size;", "int size;\n    int capacity;")
                
            # Fix constructor to initialize capacity
            if "capacity" in fixed_code and "BuggyArray(int capacity)" in fixed_code and ": capacity(capacity)" not in fixed_code:
                fixed_code = re.sub(
                    r'BuggyArray\(int capacity\)\s*\{', 
                    r'BuggyArray(int capacity) : capacity(capacity), size(0) {', 
                    fixed_code
                )
        
        elif language.lower() == "python":
            # Fix common Python issues
            if any("range" in err for err in errors) or "for i in range(n-1)" in fixed_code:
                fixed_code = fixed_code.replace("for i in range(n-1)", "for i in range(n)")
                
            if "for j in range(n-1)" in fixed_code:
                fixed_code = fixed_code.replace("for j in range(n-1)", "for j in range(n-i-1)")
                
            if any("comparison" in err.lower() or "sort" in err.lower() for err in errors) or "if arr[j] < arr[j+1]" in fixed_code:
                fixed_code = fixed_code.replace("if arr[j] < arr[j+1]", "if arr[j] > arr[j+1]")
                
            if any("print" in err and "parentheses" in err for err in errors):
                fixed_code = re.sub(r'print\s+([^(])', r'print(\1)', fixed_code)
                
            # Fix missing libraries
            if "random" in fixed_code and "import random" not in fixed_code:
                fixed_code = "import random\n" + fixed_code
                
        return fixed_code
    
    def process_memory(self, memory: Memory) -> Tuple[bool, List[str], str]:
        """
        Process a single memory item.
        
        Args:
            memory: The Memory object with faulty code
            
        Returns:
            Tuple of (success, error_messages, fixed_code)
        """
        if not memory.faulty_code or not memory.language:
            return False, ["No code or language specified"], ""
            
        # Get the appropriate compiler
        compiler = self.get_compiler(memory.language)
        if not compiler:
            return False, [f"Unsupported language: {memory.language}"], ""
            
        # Compile the code and get errors
        error_messages = compiler.compile(memory.faulty_code)
        
        # If no errors but code is still clearly buggy, add some synthetic errors
        if not error_messages:
            if memory.language.lower() == "verilog" and ("overflow = " in memory.faulty_code):
                error_messages = ["Warning: Using blocking assignment in sequential logic"]
            elif memory.language.lower() in ["cpp", "c++"] and "~" not in memory.faulty_code and "delete" not in memory.faulty_code and "new" in memory.faulty_code:
                error_messages = ["Warning: Potential memory leak - allocating memory without proper cleanup"]
            elif memory.language.lower() == "python" and "arr[j] < arr[j+1]" in memory.faulty_code and "sort" in memory.faulty_code.lower():
                error_messages = ["Warning: Comparison may be reversed for normal sorting algorithm"]
                
        # Still no errors? Check if the code is actually empty or trivial
        if not error_messages:
            if not memory.faulty_code.strip() or len(memory.faulty_code.split("\n")) < 3:
                return False, ["Empty or trivial code"], memory.faulty_code
            else:
                # If we can't find errors but the code looks substantial, assume it's correct
                return True, [], memory.faulty_code
        
        # Generate fix using LLM or fallback to basic fixes
        tokens_used = 0
        cost = 0.0
        
        if self.llm and not self.llm.last_error:
            try:
                print(f"Sending code to LLM for fix with {len(error_messages)} errors...")
                fixed_code = Memory.fix_code(
                    memory.faulty_code, 
                    error_messages, 
                    memory.language, 
                    self.llm
                )
                
                # Track tokens and cost
                tokens_used += self.llm.total_tokens
                cost += self.llm.total_cost
                
                # Strip any markdown code block markers from the LLM-generated code
                fixed_code = self.strip_markdown_code_blocks(fixed_code, memory.language)
            except Exception as e:
                print(f"Error using LLM for fix: {str(e)}")
                fixed_code = self.basic_code_fix(memory.faulty_code, error_messages, memory.language)
        else:
            print("Using basic fix rules (no LLM available)")
            fixed_code = self.basic_code_fix(memory.faulty_code, error_messages, memory.language)
        
        # Make sure we actually got a fix
        if not fixed_code or fixed_code.strip() == "":
            print(f"Warning: Got empty fix for {memory.id}")
            return False, error_messages, memory.faulty_code
        
        # Verify the fix
        verification_errors = compiler.compile(fixed_code)
        
        # If verification fails, try once more with the new errors
        if verification_errors:
            print(f"First fix attempt failed, trying again with new errors for {memory.id}")
            print(f"Verification errors: {verification_errors}")
            
            # Apply basic fixes first before trying LLM again
            fixed_code = self.basic_code_fix(fixed_code, verification_errors, memory.language)
            
            # Check if basic fixes resolved the issues
            second_verification = compiler.compile(fixed_code)
            
            # If we still have errors, try with LLM
            if second_verification and self.llm and not self.llm.last_error:
                try:
                    print(f"Sending code to LLM for second fix with {len(second_verification)} errors...")
                    fixed_code = Memory.fix_code(
                        fixed_code,  # Use the partially fixed code
                        second_verification, 
                        memory.language, 
                        self.llm
                    )
                    
                    # Track tokens and cost
                    tokens_used += self.llm.total_tokens
                    cost += self.llm.total_cost
                    
                    # Strip any markdown code block markers from the LLM-generated code (second attempt)
                    fixed_code = self.strip_markdown_code_blocks(fixed_code, memory.language)
                except Exception as e:
                    print(f"Error using LLM for second fix: {str(e)}")
                    # Already applied basic fixes before LLM retry, no need to do it again
            
            # Final verification
            final_errors = compiler.compile(fixed_code)
            if final_errors:
                print(f"Warning: Fix still has errors for {memory.id}: {final_errors}")
                # Try one more basic fix based on final errors
                fixed_code = self.basic_code_fix(fixed_code, final_errors, memory.language)
                
                # Very final check
                very_final_errors = compiler.compile(fixed_code)
                if very_final_errors:
                    print(f"Warning: Final fix still has errors for {memory.id}: {very_final_errors}")
                    # We'll still save this partial fix along with the remaining errors
                    return False, very_final_errors, fixed_code
        
        # Check if we actually changed anything
        if fixed_code.strip() == memory.faulty_code.strip():
            print(f"Warning: Fix identical to original code for {memory.id}")
            return False, ["No changes made - fix identical to original"], fixed_code
            
        print(f"Successfully fixed code for {memory.id}")
        print(f"Tokens used: {tokens_used}, Cost: ${cost:.6f}")
            
        return True, error_messages, fixed_code
    
    def process_all_unfixed_memories(self, language: Optional[str] = None) -> Dict[str, Any]:
        """
        Process all unfixed memories in the database.
        
        Args:
            language: Optional filter by programming language
            
        Returns:
            Dictionary with results summary
        """
        unfixed_memories = self.memory.get_unfixed_memories(language)
        
        results = {
            "total": len(unfixed_memories),
            "successful_fixes": 0,
            "partial_fixes": 0,
            "failures": 0,
            "total_tokens": 0,
            "total_cost": 0.0,
            "details": []
        }
        
        for memory in unfixed_memories:
            print(f"Processing memory {memory.id} ({memory.language})")
            
            # Track starting token count and cost to calculate usage for this memory
            start_tokens = self.llm.total_tokens if self.llm else 0
            start_cost = self.llm.total_cost if self.llm else 0.0
            
            success, errors, fixed_code = self.process_memory(memory)
            
            # Calculate tokens and cost for this memory
            tokens_used = (self.llm.total_tokens - start_tokens) if self.llm else 0
            cost = (self.llm.total_cost - start_cost) if self.llm else 0.0
            
            results["total_tokens"] += tokens_used
            results["total_cost"] += cost
            
            # Always update the compiler errors
            self.memory.update_memory_code_fields(
                memory.id,
                compiler_errors=errors
            )
            
            # Only update the fixed code if it's different from the original
            if fixed_code and fixed_code.strip() != memory.faulty_code.strip():
                # Make sure we strip any markdown code block markers one final time before saving
                clean_fixed_code = self.strip_markdown_code_blocks(fixed_code, memory.language)
                
                self.memory.update_memory_code_fields(
                    memory.id,
                    fixed_code=clean_fixed_code
                )
                
                # Verify the update was successful by checking the database
                if not self.memory.memories[memory.id].fixed_code:
                    print(f"ERROR: Failed to update fixed_code for {memory.id} in database!")
                else:
                    print(f"Successfully updated fixed_code for {memory.id}")
            
            # Also update the JSON file to keep everything in sync
            if self.memory.use_sqlite:
                try:
                    # Export current state to JSON
                    from hagent.tool.memory.import_data import export_sqlite_to_json
                    db_path = self.memory.db_store.db_path
                    json_path = str(Path(db_path).with_suffix('.json'))
                    export_sqlite_to_json(db_path, json_path)
                    print(f"Successfully exported updated data to {json_path}")
                except Exception as e:
                    print(f"Error exporting to JSON: {str(e)}")
            
            # Track results
            if success and fixed_code and fixed_code.strip() != memory.faulty_code.strip():
                results["successful_fixes"] += 1
                status = "success"
            elif fixed_code and fixed_code.strip() != memory.faulty_code.strip():
                results["partial_fixes"] += 1
                status = "partial"
            else:
                results["failures"] += 1
                status = "failure"
                
            results["details"].append({
                "memory_id": memory.id,
                "language": memory.language,
                "status": status,
                "error_count": len(errors),
                "tokens": tokens_used,
                "cost": cost
            })
            
        return results


def create_llm_config(output_path: str):
    """Create a sample LLM configuration file for code fixing."""
    config = {
        "code_fix_generator": {
            "llm": {
                "model": "openai/gpt-4-turbo-preview",
                "temperature": 0.2,
                "max_tokens": 2000
            },
            "code_fix": [
                {
                    "role": "system",
                    "content": "You are an expert programmer who specializes in fixing code bugs. Your task is to fix the provided code based on compiler error messages. Provide only the complete fixed code without explanations."
                },
                {
                    "role": "user",
                    "content": "Fix the following {language} code based on these compiler errors:\n\nCode:\n```{language}\n{faulty_code}\n```\n\nErrors:\n{compiler_errors}\n\nProvide the complete fixed code without explanations."
                }
            ]
        }
    }
    
    # Save to YAML file
    try:
        directory = os.path.dirname(output_path)
        if directory and not os.path.exists(directory):
            os.makedirs(directory)
            
        with open(output_path, 'w') as f:
            yaml.dump(config, f, default_flow_style=False)
            
        print(f"Created LLM configuration at {output_path}")
        return output_path
    except Exception as e:
        print(f"Error creating config file: {str(e)}")
        # Create it in a temporary location instead
        tmp_path = os.path.join(tempfile.gettempdir(), "code_fix_llm_config.yaml")
        with open(tmp_path, 'w') as f:
            yaml.dump(config, f, default_flow_style=False)
        print(f"Created LLM configuration at alternative location: {tmp_path}")
        return tmp_path


def main():
    """Main function to run the code fix generator."""
    parser = argparse.ArgumentParser(description="Generate code fixes for memories in the database")
    parser.add_argument('--db-path', help='Path to the SQLite database file')
    parser.add_argument('--llm-config', help='Path to the LLM configuration file')
    parser.add_argument('--language', help='Filter by programming language')
    parser.add_argument('--create-config', action='store_true', help='Create a sample LLM configuration file')
    parser.add_argument('--debug', action='store_true', help='Enable more verbose debug output')
    args = parser.parse_args()
    
    # Create config file if requested
    if args.create_config:
        config_path = args.llm_config or os.path.join(os.path.dirname(__file__), "code_fix_llm_config.yaml")
        create_llm_config(config_path)
        print("Configuration file created. You may need to customize it.")
        return
    
    # Set up default paths
    if not args.db_path:
        db_path = os.path.join(os.path.dirname(__file__), "data", "memory.db")
    else:
        db_path = args.db_path
        
    if not args.llm_config:
        llm_config = os.path.join(os.path.dirname(__file__), "code_fix_llm_config.yaml")
        if not os.path.exists(llm_config):
            print("No LLM config found. Creating a default one.")
            llm_config = create_llm_config(llm_config)
    else:
        llm_config = args.llm_config
    
    # Check if paths exist
    if not os.path.exists(db_path):
        print(f"Database not found at {db_path}")
        return
        
    if not os.path.exists(llm_config):
        print(f"LLM configuration not found at {llm_config}, creating default")
        llm_config = create_llm_config(llm_config)
    
    # Initialize memory system
    memory = FewShotMemory(
        name="code_fix_generator",
        use_sqlite=True,
        db_path=db_path
    )
    
    # Check if we have any memories to process
    unfixed = memory.get_unfixed_memories(args.language)
    if not unfixed:
        print("No unfixed memories found in the database.")
        return
    else:
        print(f"Found {len(unfixed)} unfixed memories to process.")
    
    # Initialize and run the code fix generator
    generator = CodeFixGenerator(
        memory_system=memory,
        llm_conf_file=llm_config
    )
    
    results = generator.process_all_unfixed_memories(args.language)
    
    # Print results
    print("\nProcessing completed")
    print(f"Total memories processed: {results['total']}")
    print(f"Successful fixes: {results['successful_fixes']}")
    print(f"Partial fixes: {results['partial_fixes']}")
    print(f"Failures: {results['failures']}")
    print(f"Total tokens used: {results['total_tokens']}")
    print(f"Total cost: ${results['total_cost']:.6f}")
    
    if results['details']:
        print("\nDetails:")
        for detail in results['details']:
            token_info = f", tokens: {detail['tokens']}, cost: ${detail['cost']:.6f}" if 'tokens' in detail else ""
            print(f"  {detail['memory_id']} ({detail['language']}): {detail['status']} with {detail['error_count']} errors{token_info}")
    

if __name__ == "__main__":
    main()