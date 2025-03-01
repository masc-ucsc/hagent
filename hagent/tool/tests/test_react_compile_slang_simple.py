#!/usr/bin/env python3
"""
Command-line tool that reads a Verilog source file and iteratively fixes it
using React, Compile_slang, and LLM_wrap. The tool uses diagnostic messages
(like compiler.get_errors) to drive the LLM-based fix generation.
"""

import sys
import os
import argparse
import tempfile
from typing import List, Dict
import uuid

from hagent.tool.react import React
from hagent.tool.compile_slang import Compile_slang
from hagent.core.llm_wrap import LLM_wrap
from hagent.tool.compile import Diagnostic
from hagent.tool.extract_code import Extract_code_verilog


class React_compile_slang:
    """
    Encapsulates LLM and Compile_slang for iterative Verilog code fixing.
    """

    def __init__(self):
        # Determine the configuration file path.
        conf_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'llm_wrap_conf1.yaml')
        # Initialize LLM_wrap instance using configuration from file.
        self.llm = LLM_wrap(
            name='test_react_compile_slang_simple', log_file='test_react_compile_slang_simple.log', conf_file=conf_file
        )
        assert not self.llm.last_error

        self.compiler = Compile_slang()
        self.extractor = Extract_code_verilog()

    def check_callback(self, code: str) -> List[Diagnostic]:
        """
        Checks whether the provided Verilog code compiles.
        Calls setup on the compiler to reset its state.
        Returns a list of Diagnostic objects if errors are found.
        """
        if not self.compiler.setup():  # Reset compiler state.
            return []
        if not self.compiler.add_inline(code):  # Add code to compiler.
            return []
        return self.compiler.get_errors()

    def fix_callback(
        self, current_text: str, diag: Diagnostic, fix_example: Dict[str, str], delta: bool, iteration_count: int
    ) -> str:
        """
        Uses the LLM to generate a fixed version of the current code.
        If a fix_example is provided, it is merged with the current code.
        """
        if not diag:  # It should not happen, but just in case
            return current_text

        if not fix_example:
            results = self.llm.inference({'code': current_text}, 'direct_prompt', n=1)
        else:
            # Merge fix_example with the current code for the prompt.
            results = self.llm.inference({**fix_example, 'code': current_text}, 'example_prompt', n=1)

        line = diag.loc
        best_code = current_text
        for res in results:
            code = self.extractor.parse(res)
            if code:
                code_diags = self.check_callback(code)
                if not code_diags:
                    return code
                if code_diags[0].loc > line:
                    line = code_diags[0].loc
                    best_code = code

        return best_code


def test_react_with_corrupt_db():
    """Test React with a corrupt database file."""
    # Create a temporary DB file with corrupt content
    with tempfile.NamedTemporaryFile(delete=False, suffix='.yaml') as tmp:
        tmp_name = tmp.name
        # Write corrupt YAML
        tmp.write(b"error_type1: 'not a dict'\n")
    
    try:
        # Initialize React with the corrupt DB file
        react = React()
        setup_success = react.setup(db_path=tmp_name, learn=False)
        # The current implementation doesn't validate the structure of the DB
        # It just loads whatever is in the file, so this should return True
        assert setup_success, "Setup should succeed with corrupt DB structure"
        
        print("Test with corrupt DB passed!")
    finally:
        # Clean up
        if os.path.exists(tmp_name):
            os.remove(tmp_name)


def test_react_with_nonexistent_db_file():
    """Test React with a non-existent database file."""
    # Use a non-existent file path that definitely doesn't exist
    non_existent_path = f"non_existent_db_file_{uuid.uuid4()}.yaml"
    
    # Initialize React with the non-existent DB file
    react = React()
    
    # Test with learn mode disabled
    setup_success = react.setup(db_path=non_existent_path, learn=False)
    assert not setup_success, "Setup should fail with non-existent DB and learn=False"
    assert "Database file not found" in react.error_message
    
    # Test with learn mode enabled
    setup_success = react.setup(db_path=non_existent_path, learn=True)
    assert setup_success, "Setup should succeed with non-existent DB and learn=True"
    
    # Clean up any created file
    if os.path.exists(non_existent_path):
        os.remove(non_existent_path)
    
    print("Test with non-existent DB file passed!")


def test_react_save_db():
    """Test React's ability to save the database."""
    # Create a temporary DB file
    with tempfile.NamedTemporaryFile(delete=False, suffix='.yaml') as tmp:
        tmp_name = tmp.name
    
    try:
        # Initialize React with the DB file and learn mode enabled
        react = React()
        setup_success = react.setup(db_path=tmp_name, learn=True)
        assert setup_success, f"React setup failed: {react.error_message}"
        
        # Add an error example
        react._add_error_example("test_error", "test_question", "test_answer")
        
        # Re-initialize React to load from the saved DB
        react2 = React()
        setup_success = react2.setup(db_path=tmp_name, learn=False)
        assert setup_success, f"React setup failed: {react2.error_message}"
        
        # Check if the error example was saved
        assert "test_error" in react2._db, "Error example not saved to DB"
        assert react2._db["test_error"]["fix_question"] == "test_question", "Fix question not saved correctly"
        assert react2._db["test_error"]["fix_answer"] == "test_answer", "Fix answer not saved correctly"
        
        print("Test save DB passed!")
    finally:
        # Clean up
        if os.path.exists(tmp_name):
            os.remove(tmp_name)


def main():
    # Run the tests
    test_react_with_corrupt_db()
    test_react_with_nonexistent_db_file()
    test_react_save_db()
    
    parser = argparse.ArgumentParser(description='Iteratively fix Verilog code using React, Compile_slang, and LLM_wrap.')
    parser.add_argument('verilog_file', help='Path to the Verilog source file')
    args = parser.parse_args()

    # Read Verilog source code from the provided file.
    try:
        with open(args.verilog_file, 'r') as f:
            initial_code = f.read()
    except Exception as e:
        print(f"Error reading file '{args.verilog_file}': {e}", file=sys.stderr)
        sys.exit(1)

    # Initialize and set up the React tool.
    react = React()
    if not react.setup(db_path='dummy_db.yaml', learn=True, max_iterations=5):
        print(f'React setup failed: {react.error_message}', file=sys.stderr)
        sys.exit(1)

    react_compiler = React_compile_slang()

    # Drive the Re-Act cycle.
    fixed_code = react.react_cycle(
        initial_text=initial_code, check_callback=react_compiler.check_callback, fix_callback=react_compiler.fix_callback
    )

    if not fixed_code:
        print('Unable to fix the Verilog code within the iteration limit.', file=sys.stderr)
        sys.exit(1)

    # Final check: ensure that the fixed code compiles.
    final_errors = react_compiler.check_callback(fixed_code)
    if final_errors:
        error_details = '\n'.join([f'Error: {d.msg} at {d.loc}. Hint: {d.hint}' for d in final_errors])
        print(fixed_code)
        print('Final code still contains errors:', file=sys.stderr)
        print(error_details, file=sys.stderr)
        sys.exit(1)

    print('Fixed Verilog code:')
    print(fixed_code)
    sys.exit(0)


if __name__ == '__main__':
    main()
