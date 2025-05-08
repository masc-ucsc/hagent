# hagent/tool/memory/react_memory.py

from typing import Optional, Callable, List, Dict, Tuple
import os
from pathlib import Path

from hagent.tool.compile import Diagnostic
from hagent.tool.memory.few_shot_memory_layer import FewShotMemory, Memory
from hagent.tool.memory.utils import normalize_code


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


class ReactMemory:
    """
    Enhanced Re-Act iteration logic with FewShotMemory integration.
    Orchestrates iterative error fixing by invoking user-supplied check and fix callbacks
    while leveraging a memory system for better few-shot learning.
    """

    def __init__(self):
        # Initialize internal state
        self.error_message: str = ''
        self._is_ready: bool = False
        self._db_path: Optional[str] = None
        self._learn_mode: bool = False
        self._max_iterations: int = 5
        self.last_code: str = ''
        self._log: List[Dict] = []  # Records iteration details
        self._lang_prefix: str = '//'
        
        # FewShotMemory integration
        self._memory_system: Optional[FewShotMemory] = None

    def setup(
        self, db_path: Optional[str] = None, learn: bool = False, max_iterations: int = 5, comment_prefix: str = '//'
    ) -> bool:
        """
        Prepares the React tool for usage with FewShotMemory integration.
        - Clears internal state.
        - Loads or initializes the Memory system.
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
        self._db_path = db_path

        if self._db_path:
            try:
                # Initialize FewShotMemory with the database path
                self._memory_system = FewShotMemory(
                    db_path=self._db_path,
                    auto_create_data=self._learn_mode
                )
                
                # Check if we have memories loaded
                if not self._memory_system.memories and not self._learn_mode:
                    self.error_message = 'Database file not found or empty, and learn mode is disabled.'
                    self._is_ready = False
                    return False
                    
            except Exception as e:
                self.error_message = f'Failed to initialize memory system: {e}'
                self._is_ready = False
                return False
        else:
            # Create memory system with default settings
            try:
                # Use a default path in the data directory
                data_dir = Path("data")
                data_dir.mkdir(exist_ok=True)
                default_db_path = str(data_dir / "react_memory_database.yaml")
                
                self._db_path = default_db_path
                self._memory_system = FewShotMemory(
                    db_path=default_db_path,
                    auto_create_data=self._learn_mode
                )
            except Exception as e:
                self.error_message = f'Failed to create memory system: {e}'
                self._is_ready = False
                return False

        self._is_ready = True
        return True

    def _find_error_example(self, error_type: str) -> Dict[str, str]:
        """
        Find a memory example for a specific error type using FewShotMemory's find method.
        
        Args:
            error_type: The type of error to search for
            
        Returns:
            Dictionary with fix_question and fix_answer keys
        """
        if not self._memory_system:
            return {'fix_question': '', 'fix_answer': ''}
        
        matching_memories = []
        
        # First try direct attribute matching, which works with test mocks
        for memory in self._memory_system.memories.values():
            if memory.error_type == error_type and memory.fixed_code:
                matching_memories.append(memory)
                
        # If no direct matches and it's not a test mock environment, use semantic search
        if not matching_memories and hasattr(self._memory_system, 'find'):
            try:
                # Create a simple query that includes the error type
                query_code = f"// Error type: {error_type}"
                
                # Only try semantic search if we're not in a test mock environment
                if hasattr(self._memory_system, 'model') and self._memory_system.model is not None:
                    # Use FewShotMemory's find method to get relevant examples
                    matching_memories = self._memory_system.find(query_code)
            except Exception as e:
                print(f"Warning: Semantic search failed: {e}")
                # Fall back to direct search already done above
        
        if not matching_memories:
            return {'fix_question': '', 'fix_answer': ''}
        
        # Use the first matching memory
        memory = matching_memories[0]
        return {
            'fix_question': memory.faulty_code,
            'fix_answer': memory.fixed_code
        }

    def _add_error_example(self, error_type: str, fix_question: str, fix_answer: str) -> None:
        """
        Updates memory with a new error example using FewShotMemory's add method.
        Immediately saves if learning mode is enabled.
        
        Args:
            error_type: The type of error
            fix_question: The code with the error
            fix_answer: The fixed code
        """
        if not self._memory_system or not self._learn_mode:
            return
        
        # Check for duplicate entries
        exists = False
        
        # First try to check if the example already exists by direct comparison
        for memory in self._memory_system.memories.values():
            if (memory.error_type == error_type and 
                normalize_code(memory.faulty_code) == normalize_code(fix_question)):
                print(f"Skipping duplicate entry for error type: {error_type}")
                exists = True
                break
                
        # If we didn't find a direct match and find() is available, try semantic search
        if not exists and hasattr(self._memory_system, 'find'):
            try:
                # Only use find if we're not in a test mock environment
                if hasattr(self._memory_system, 'model') and self._memory_system.model is not None:
                    existing_memories = self._memory_system.find(fix_question)
                    # Check if any found memories match our code
                    for memory in existing_memories:
                        if normalize_code(memory.faulty_code) == normalize_code(fix_question):
                            print(f"Skipping duplicate entry for error type: {error_type}")
                            exists = True
                            break
            except Exception as e:
                print(f"Warning: Semantic search for duplicates failed: {e}")
                # Continue with adding since we couldn't verify duplicates
        
        if exists:
            return
            
        # Create compiler errors list for context
        compiler_errors = [f"Error type: {error_type}"]
        
        # Add to memory system - FewShotMemory.add will generate an ID and save the database
        try:
            memory_id = self._memory_system.add(
                original_code=fix_question,
                fixed_code=fix_answer,
                errors=compiler_errors
            )
            
            print(f"Added new memory with ID: {memory_id} for error type: {error_type}")
        except Exception as e:
            print(f"Warning: Failed to add to memory: {e}")
            # Don't raise the exception as this is optional functionality

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
        Orchestrates the Re-Act loop with memory integration:
          1. Calls check_callback on the current code.
          2. If no errors, returns the code immediately.
          3. If errors are found, extracts the error type and retrieves a sample fix from memory.
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
        
        print(f"Starting react_cycle with {len(initial_text)} characters of code")

        for iteration in range(1, self._max_iterations + 1):
            print(f"Iteration {iteration}/{self._max_iterations}")
            iteration_log: Dict = {'iteration': iteration, 'check': None, 'fix': None}
            
            # Get diagnostics from the check callback
            diagnostics = check_callback(current_text)
            print(f"Found {len(diagnostics)} diagnostics")
            
            # Log all diagnostic details
            iteration_log['check'] = [{'msg': d.msg, 'loc': d.loc, 'hint': getattr(d, 'hint', '')} for d in diagnostics]

            if not diagnostics:
                print("No diagnostics - code is correct")
                self._log.append(iteration_log)
                self.last_code = current_text
                return current_text

            # Get error type from first diagnostic
            error_type = diagnostics[0].msg
            print(f"Error type: {error_type}")
            
            # Find an example fix for this error type from memory
            fix_example = self._find_error_example(error_type)
            print(f"Found fix example: {bool(fix_example.get('fix_answer'))}")

            if iteration == 1:
                # First iteration - use delta approach
                print("Using delta approach for first iteration")
                try:
                    # Extract a delta around the error location
                    delta, start_line, end_line = self._get_delta(current_text, diagnostics[0].loc)
                    print(f"Delta extracted lines {start_line}-{end_line}")
                    
                    # Insert diagnostic comment
                    try:
                        annotated = diagnostics[0].insert_comment(delta, self._lang_prefix)
                        print("Successfully inserted diagnostic comment")
                    except Exception as e:
                        self.error_message = f'Failed to insert diagnostic comment in delta: {e}'
                        print(f"ERROR: {self.error_message}")
                        self._log.append(iteration_log)
                        return ''
                    
                    # Call fix callback with delta
                    fixed_delta = fix_callback(annotated, diagnostics[0], fix_example, True, iteration)
                    if fixed_delta == annotated:
                        print("Fix callback didn't change the code")
                    else:
                        print(f"Fix callback returned {len(fixed_delta)} characters")
                    
                    fix_question = annotated
                    fix_answer = fixed_delta
                    
                    # Apply the fixed delta to the full code
                    new_text = self._apply_patch(current_text, fixed_delta, start_line, end_line)
                except Exception as e:
                    self.error_message = f'Error in delta processing: {e}'
                    print(f"ERROR: {self.error_message}")
                    self._log.append(iteration_log)
                    return ''
            else:
                # Subsequent iterations - use full code approach
                print("Using full code approach")
                try:
                    # Insert diagnostic comment
                    try:
                        annotated = diagnostics[0].insert_comment(current_text, self._lang_prefix)
                        print("Successfully inserted diagnostic comment")
                    except Exception as e:
                        self.error_message = f'Failed to insert diagnostic comment: {e}'
                        print(f"ERROR: {self.error_message}")
                        self._log.append(iteration_log)
                        return ''
                    
                    # Call fix callback with full code
                    new_text = fix_callback(annotated, diagnostics[0], fix_example, False, iteration)
                    if new_text == annotated:
                        print("Fix callback didn't change the code")
                    else:
                        print(f"Fix callback returned {len(new_text)} characters")
                    
                    fix_question = annotated
                    fix_answer = new_text
                except Exception as e:
                    self.error_message = f'Error in full code processing: {e}'
                    print(f"ERROR: {self.error_message}")
                    self._log.append(iteration_log)
                    return ''

            # Log the fix attempt
            iteration_log['fix'] = new_text

            # Check if the fix worked
            new_diagnostics = check_callback(new_text)
            iteration_log['post_check'] = [{'msg': d.msg, 'loc': d.loc, 'hint': getattr(d, 'hint', '')} for d in new_diagnostics]
            print(f"After fix: {len(new_diagnostics)} diagnostics")
            
            # Add log entry
            self._log.append(iteration_log)

            if not new_diagnostics:
                # Success! No more errors
                print("Fix successful - no more diagnostics")
                if self._learn_mode:
                    self._add_error_example(error_type, fix_question, fix_answer)
                    print(f"Added error example for: {error_type}")
                self.last_code = new_text
                return new_text
            elif current_text == new_text:
                # No change in the code - we're stuck
                print("Fix didn't change the code - breaking loop")
                self.error_message = "Fix didn't make any changes to the code"
                self.last_code = current_text
                break
            else:
                # There are still errors, but the code changed
                new_error_type = new_diagnostics[0].error
                if new_error_type != error_type and self._learn_mode:
                    # We fixed one error but encountered another
                    print(f"Error type changed from {error_type} to {new_error_type}")
                    self._add_error_example(error_type, fix_question, fix_answer)
                    print(f"Added error example for: {error_type}")
                
                # Continue with the new code
                current_text = new_text
                print("Continuing with modified code")

        # If we get here, we've exceeded the iteration limit without fixing the code
        print(f"Reached max iterations ({self._max_iterations}) without fixing all issues")
        self.last_code = current_text
        return ''

    def get_log(self) -> List[Dict]:
        """
        Returns the log of the iterations.
        """
        return self._log