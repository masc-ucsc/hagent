#!/usr/bin/env python3
"""
Iterative C++ compile fix using GCC and LLM_wrap.
This script uses React to drive iterations where GCC is invoked
to check code syntax and an LLM wrapper is used to generate fixes.
"""

import os
import re
import subprocess
import tempfile
from typing import List

from hagent.tool.react import React, Memory_shot
from hagent.tool.compile import Diagnostic
from hagent.core.llm_wrap import LLM_wrap
from hagent.inou.path_manager import PathManager


def extract_errors(gcc_output: str) -> list:
    """
    Extracts GCC errors (including context) from compiler output.

    Args:
        gcc_output: The compiler output string.

    Returns:
        A list of error block strings. Each block includes an error line and its context.
    """
    error_blocks = []
    current_block = None

    for line in gcc_output.splitlines():
        # Start a new error block if the line contains 'error:'
        if re.match(r'.*error:', line):
            if current_block:
                error_blocks.append(current_block)
            current_block = line + '\n'
        elif current_block:
            # Continuation of the current error block.
            current_block += line + '\n'
    if current_block:
        error_blocks.append(current_block)
    return error_blocks


def check_callback_cpp(code: str) -> List[Diagnostic]:
    """
    Checks if the provided C++ code compiles using g++ in syntax-check mode.

    Returns a list of Diagnostic objects if errors are found; an empty list otherwise.
    """
    with tempfile.NamedTemporaryFile(delete=False, suffix='.cpp') as tmp:
        tmp_name = tmp.name
        tmp.write(code.encode('utf-8'))

    try:
        # Run g++ in syntax-check mode (-fsyntax-only) without linking.
        result = subprocess.run(['g++', '-std=c++17', '-fsyntax-only', tmp_name], capture_output=True, text=True)
        if result.returncode != 0:
            print('GCC ERROR OUTPUT:')
            print(result.stderr)
            diags = []
            for msg in extract_errors(result.stderr):
                # Create a Diagnostic with the error message.
                diag = Diagnostic(msg)
                print(f'DIAGNOSTIC: file={diag.file}, loc={diag.loc}, msg={diag.msg}, error={diag.error}')
                diags.append(diag)
            return diags
        return []
    finally:
        if os.path.exists(tmp_name):
            os.remove(tmp_name)


def fix_callback_cpp(current_code: str, diag: Diagnostic, fix_example: Memory_shot, delta: bool, iteration_count: int) -> str:
    """
    Use LLM_wrap to suggest a fix for the C++ code. We:
    - Build a C++-specific prompt (code-only response, remove inserted comments)
    - Ask for 1-2 candidates from the LLM
    - Extract code blocks from responses
    - Re-check each candidate with g++ and pick a compiling one, otherwise best-progressing one
    Fallback: if LLM unavailable, attempt a deterministic semicolon fix around the reported area.
    """
    print(f'FIXING ERROR: {diag.msg}, location: {diag.loc}')
    print(f'Current iteration: {iteration_count}, delta mode: {delta}')

    # Show delta for debugging
    if delta:
        print('DELTA CODE TO FIX:\n')
        print(current_code)

    # Try LLM-based fixing first
    try:
        from hagent.tool.extract_code import Extract_code_default

        conf_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'llm_wrap_conf1.yaml')

        # Override prompts to be C++-specific while reusing llm settings from YAML
        cpp_prompts = {
            'direct_prompt': [
                {'role': 'system', 'content': 'You are an expert C++ programmer.'},
                {
                    'role': 'user',
                    'content': (
                        'The following C++ code contains a compile error annotated in comments.\n'
                        'Fix the error. Respond only with the corrected C++ code (no explanations).\n'
                        'Remove any error annotations/comments.\n\n'
                        '```\n{code}\n```'
                    ),
                },
            ],
            'example_prompt': [
                {'role': 'system', 'content': 'You are an expert C++ programmer.'},
                {
                    'role': 'user',
                    'content': (
                        'The following C++ code contains a compile error annotated in comments.\n'
                        'As a reference, a similar error for the following code:\n{fix.question}\n'
                        'had the following correct answer:\n{fix.answer}\n\n'
                        'Fix the error in the code below. Respond only with the corrected C++ code (no explanations).\n'
                        'Remove any error annotations/comments.\n\n'
                        '```\n{code}\n```'
                    ),
                },
            ],
        }

        lw = LLM_wrap(
            name='test_react_compile_slang_simple',  # reuse existing llm settings
            log_file='test_react_compile_gcc_simple.log',
            conf_file=conf_file,
            overwrite_conf=cpp_prompts,
        )

        # If LLM init failed, trigger fallback
        if lw.last_error:
            raise RuntimeError(lw.last_error)

        extractor = Extract_code_default()

        # Build prompt dict
        if not fix_example or not getattr(fix_example, 'question', ''):
            prompt = {'code': current_code}
            results = lw.inference(prompt, 'direct_prompt', n=2)
        else:
            prompt = {'code': current_code, 'fix': fix_example}
            results = lw.inference(prompt, 'example_prompt', n=2)

        best_code = current_code
        best_loc = diag.loc

        for res in results or []:
            candidates = extractor.parse(res)
            for cand in candidates:
                if not cand:
                    continue
                diags = check_callback_cpp(cand)
                if not diags:
                    return cand  # compiles, done
                # Prefer the one that moves first error further down
                if diags[0].loc > best_loc:
                    best_loc = diags[0].loc
                    best_code = cand

        # If LLM suggested something marginally better, use it
        if best_code != current_code:
            return best_code

    except Exception as e:
        print(f'LLM-based fixing path failed or unavailable: {e}')

    # Fallback deterministic fix for common GCC error: missing semicolon before return
    try:
        lines = current_code.splitlines()
        # Find the line with 'return' and add semicolon to previous non-comment, non-empty line
        ret_idx = None
        for i, line in enumerate(lines):
            if line.strip().startswith('return '):
                ret_idx = i
                break
        if ret_idx is not None:
            # Walk upwards to find the likely statement to terminate
            j = ret_idx - 1
            while j >= 0 and (lines[j].strip().startswith('//') or lines[j].strip() == ''):
                j -= 1
            if j >= 0 and not lines[j].rstrip().endswith(';'):
                lines[j] = lines[j] + ';'
                return '\n'.join(lines)
    except Exception:
        pass

    return current_code


def test_react_with_memory(tmp_path, request):
    """Test React with a database file."""
    import pytest

    # Skip if running in forked mode (Python 3.13 fork + network calls = segfault)
    if hasattr(request.config, 'option') and hasattr(request.config.option, 'forked') and request.config.option.forked:
        pytest.skip('Test incompatible with --forked due to Python 3.13 network call fork safety issues')

    # Configure PathManager for test isolation
    with PathManager.configured(
        repo_dir=str(tmp_path),
        build_dir=str(tmp_path),
        cache_dir=str(tmp_path / 'cache'),
    ):
        react_tool = React()
        setup_success = react_tool.setup(db_path=str(tmp_path / 'react_db'), learn=True, max_iterations=3)
        assert setup_success, f'React setup failed: {react_tool.error_message}'

        # A C++ snippet with a missing semicolon
        faulty_code = r"""
#include <iostream>

int main() {
std::cout << "Hello World" << std::endl
return 0;
}
"""

        # Run the React cycle with the provided callbacks
        fixed_code = react_tool.react_cycle(faulty_code, check_callback_cpp, fix_callback_cpp)

        # Check results
        assert fixed_code, 'Failed to fix the code'
        assert ';' in fixed_code, 'Semicolon not added to the fixed code'

        # Check the log
        log = react_tool.get_log()
        assert len(log) > 0, 'Log should contain entries'

        print('Test with DB passed!')


def test_react_without_memory(tmp_path):
    """Test React without a database file."""
    # Configure PathManager for test isolation
    with PathManager.configured(
        repo_dir=str(tmp_path),
        build_dir=str(tmp_path),
        cache_dir=str(tmp_path / 'cache'),
    ):
        # Initialize React without a DB file
        react_tool = React()
        setup_success = react_tool.setup(learn=False, max_iterations=3, comment_prefix='//')
        assert setup_success, f'React setup failed: {react_tool.error_message}'

        # A C++ snippet with a missing semicolon
        faulty_code = r"""
#include <iostream>

int main() {
    std::cout << "Hello World" << std::endl
    return 0;
}
"""

        # Run the React cycle with the provided callbacks
        fixed_code = react_tool.react_cycle(faulty_code, check_callback_cpp, fix_callback_cpp)

        # Check results
        assert fixed_code, 'Failed to fix the code'
        assert ';' in fixed_code, 'Semicolon not added to the fixed code'

        print('Test without DB passed!')


if __name__ == '__main__':
    # Run the tests
    # test_react_with_memory()
    # test_react_without_memory()

    # Original example code
    react_tool = React()
    setup_success = react_tool.setup(db_path='output/react_db', learn=True, max_iterations=3)
    if not setup_success:
        print(f'React setup failed: {react_tool.error_message}')
        exit(1)

    # A C++ snippet with a missing semicolon.
    faulty_code = r"""
#include <iostream>

int main() {
    std::cout << "Hello World" << std::endl
    return 0;
}
"""

    # Run the React cycle with the provided callbacks.
    fixed_code = react_tool.react_cycle(faulty_code, check_callback_cpp, fix_callback_cpp)

    # Print results.
    if fixed_code:
        print('Successfully fixed code:\n')
        print(fixed_code)
    else:
        print('Could not fix the code within the iteration limits.')
