# hagent/tool/react.py

from typing import Optional, Callable, List, Dict, Tuple
import os
from ruamel.yaml import YAML
from ruamel.yaml.scalarstring import LiteralScalarString
from pathlib import Path

from hagent.tool.compile import Diagnostic
from hagent.tool.memory import FewShotMemory


def process_multiline_strings(obj):
    """
    Recursively converts strings containing newlines into a LiteralScalarString
    so that ruamel.yaml outputs them in literal block style.
    """
    if isinstance(obj, dict):
        return {k: process_multiline_strings(v) for k, v in obj.items()}
    elif isinstance(obj, list):
        return [process_multiline_strings(item) for item in obj]
    elif isinstance(obj, str) and '\n' in obj:
        # Wrap the string to enforce literal block style.
        return LiteralScalarString(obj)
    return obj


def insert_comment(code: str, add: str, prefix: str, loc: int) -> str:
    """
    Inserts a multi-line comment into a string of code at a specific line number.

    Args:
        code: The original multi-line string of code.
        add: The multi-line string containing the comment to be added.
        prefix: The comment prefix (e.g., "#" for Python, "//" for C/C++).
        loc: The line number (1-based index) where the comment should be inserted.

    Returns:
        The modified string of code with the comment inserted.
    """
    code_lines = code.splitlines(keepends=True)
    add_lines = add.splitlines()
    if loc < 1 or loc > len(code_lines) + 1:
        raise ValueError('Invalid line number (loc)')
    # Create commented lines
    commented_add_lines = [f'{prefix} {line.rstrip()}\n' for line in add_lines]
    # Insert commented lines at the specified location
    code_lines[loc - 1 : loc - 1] = commented_add_lines
    return ''.join(code_lines)


class React:
    """
    Handles Re-Act iteration logic for external tools (e.g., compilers).
    Orchestrates iterative error fixing by invoking user-supplied check and fix callbacks.
    """

    def __init__(self):
        # Initialize internal state
        self.error_message: str = ''
        self._is_ready: bool = False
        self._memory: Optional[FewShotMemory] = None
        self._learn_mode: bool = False
        self._max_iterations: int = 5
        self.last_code: str = ''
        self._log: List[Dict] = []  # Records iteration details
        self._lang_prefix: str = '//'

    def setup(
        self, db_path: Optional[str] = None, learn: bool = False, max_iterations: int = 5, comment_prefix: str = '//'
    ) -> bool:
        """
        Prepares the React tool for usage.
        - Clears internal state.
        - Initializes the memory system.
        - Configures learn mode, iteration limit, and comment prefix.
        - Sets _is_ready if successful.

        Returns:
            True if setup is successful, False otherwise (and sets error_message).
        """
        self.last_code = ''
        self._log.clear()
        self._learn_mode = learn
        self._max_iterations = max_iterations
        self._lang_prefix = comment_prefix

        try:
            # Initialize memory system with provided database path
            if db_path:
                # Check if file exists - for backward compatibility with tests
                if not learn and not os.path.exists(db_path):
                    self.error_message = 'Database file not found and learn mode is disabled.'
                    self._is_ready = False
                    return False
                    
                # Ensure parent directory exists
                db_path_obj = Path(db_path)
                db_path_obj.parent.mkdir(parents=True, exist_ok=True)
                
                self._memory = FewShotMemory(
                    db_path=db_path,
                    auto_create_data=learn  # Only create data if in learn mode
                )
                
            else:
                # Create an in-memory instance if no path is provided
                self._memory = FewShotMemory(auto_create_data=False)
            
            self._is_ready = True
            return True
        except Exception as e:
            self.error_message = f'Failed to initialize memory system: {e}'
            self._is_ready = False
            return False

    # Memory system handles database loading and saving
    
    def _get_delta(self, code: str, loc: int, window: int = 5) -> Tuple[str, int, int]:
        """
        Extracts a delta (subset of code lines) around a specified location.

        Returns:
            A tuple of (delta code, start line, end line) where start_line and end_line
            are 1-indexed boundaries within the full code.
        """
        lines = code.splitlines(keepends=True)
        total = len(lines)
        start_line = max(1, loc - window)
        end_line = min(total, loc + window)
        delta = ''.join(lines[start_line - 1 : end_line])
        return delta, start_line, end_line

    def _apply_patch(self, full_code: str, patch: str, start_line: int, end_line: int) -> str:
        """
        Applies a patch (delta) to the full code, replacing lines from start_line to end_line.
        """
        full_lines = full_code.splitlines(keepends=True)
        patch_lines = patch.splitlines(keepends=True)
        new_lines = full_lines[: start_line - 1] + patch_lines + full_lines[end_line:]
        return ''.join(new_lines)

    def react_cycle(
        self,
        initial_text: str,
        check_callback: Callable[[str], List[Diagnostic]],
        fix_callback: Callable[[str, Diagnostic, Dict[str, str], bool, int], str],
    ) -> str:
        """
        Orchestrates the Re-Act loop:
          1. Calls check_callback on the current code.
          2. If no errors, returns the code immediately.
          3. If errors are found, extracts the error type and retrieves a sample fix (if any).
          4. Inserts a multi-line comment (with all diagnostic details) into the code.
          5. On the first iteration, passes only a delta (a few lines around the error)
             to fix_callback. If that fix does not work, applies the returned patch to the
             full code. Subsequent iterations pass the full code.
          6. Calls fix_callback to obtain a proposed fix.
          7. Checks if progress is made or if iteration limit is reached.
          8. Optionally learns new error examples if learning is enabled.
          9. Returns the text that is error–free or an empty string if unable to fix.
        """
        if not self._is_ready:
            self.error_message = 'React tool is not ready. Please run setup first.'
            return ''

        current_text = initial_text
        self.last_code = initial_text

        for iteration in range(1, self._max_iterations + 1):
            iteration_log: Dict = {'iteration': iteration, 'check': None, 'fix': None}
            diagnostics = check_callback(current_text)
            # Log all diagnostic details.
            iteration_log['check'] = [{'msg': d.msg, 'loc': d.loc, 'hint': getattr(d, 'hint', '')} for d in diagnostics]

            if not diagnostics:
                self._log.append(iteration_log)
                self.last_code = current_text
                return current_text

            error_type = diagnostics[0].msg
            
            # Find similar examples from memory
            similar_examples = self._memory.find(err=diagnostics[0], fix_question=current_text)
            fix_example = {"fix_question": "", "fix_answer": ""}
            if similar_examples:
                # Use the best match from memory
                best_match = similar_examples[0]
                fix_example = {
                    "fix_question": best_match.faulty_code,
                    "fix_answer": best_match.fix_answer
                }
            assert isinstance(fix_example, dict), 'Memory result corrupted'

            if iteration == 1:
                # Use a delta: only a few lines around the first error.
                delta, start_line, end_line = self._get_delta(current_text, diagnostics[0].loc)
                try:
                    annotated = diagnostics[0].insert_comment(delta, self._lang_prefix)
                except Exception as e:
                    self.error_message = f'Failed to insert diagnostic comment in delta: {e}'
                    self._log.append(iteration_log)
                    return ''
                fixed_delta = fix_callback(annotated, diagnostics[0], fix_example, True, iteration)
                fix_question = annotated
                fix_answer = fixed_delta
                # Apply the returned patch to the full code.
                new_text = self._apply_patch(current_text, fixed_delta, start_line, end_line)
            else:
                # Use the full code in subsequent iterations.
                try:
                    annotated = diagnostics[0].insert_comment(current_text, self._lang_prefix)
                except Exception as e:
                    self.error_message = f'Failed to insert diagnostic comment: {e}'
                    self._log.append(iteration_log)
                    return ''
                new_text = fix_callback(annotated, diagnostics[0], fix_example, False, iteration)
                fix_question = annotated
                fix_answer = new_text

            iteration_log['fix'] = new_text

            new_diagnostics = check_callback(new_text)
            iteration_log['post_check'] = [{'msg': d.msg, 'loc': d.loc, 'hint': getattr(d, 'hint', '')} for d in new_diagnostics]
            self._log.append(iteration_log)

            if not new_diagnostics:
                if self._learn_mode:
                    memory_id = self._memory.add(diagnostics[0], fix_question, fix_answer)
                    print(f"Added fix to memory with ID: {memory_id}")
                self.last_code = new_text
                return new_text
            else:
                new_error_type = new_diagnostics[0].msg
                if new_error_type != error_type and self._learn_mode:
                    memory_id = self._memory.add(diagnostics[0], fix_question, fix_answer)
                    print(f"Added partial fix to memory with ID: {memory_id}")
                current_text = new_text

        self.last_code = current_text
        return ''

    def get_log(self) -> List[Dict]:
        """
        Returns the log of the iterations.
        """
        return self._log

    def _add_error_example(self, error_type: str, fix_question: str, fix_answer: str) -> None:
        """
        Adds an error example to the memory system using the error type as content.
        Used for backward compatibility with tests.
        
        Args:
            error_type: The type of error
            fix_question: The code with the error
            fix_answer: The fixed code
        """
        if not self._memory:
            self.error_message = "Memory system not initialized"
            return
        
        # Create a minimal diagnostic
        diagnostic = Diagnostic(error_type)
        
        # Add to memory system
        self._memory.add(
            err=diagnostic,
            fix_question=fix_question,
            fix_answer=fix_answer
        )
