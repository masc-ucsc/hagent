# hagent/tool/memory/react_memory.py

from typing import Optional, Callable, List, Dict, Tuple
import os
from ruamel.yaml import YAML
from ruamel.yaml.scalarstring import LiteralScalarString

from hagent.tool.compile import Diagnostic
from hagent.tool.memory.few_shot_memory_layer import FewShotMemory, Memory


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
        self._db_path: Optional[str] = None
        self._db: Dict[str, Dict[str, str]] = {}  # Mapping: error type -> sample fix
        self._learn_mode: bool = False
        self._max_iterations: int = 5
        self.last_code: str = ''
        self._log: List[Dict] = []  # Records iteration details
        self._lang_prefix: str = '//'
        self._memory: Optional[FewShotMemory] = None  # Memory system for semantic retrieval

    def setup(
        self, db_path: Optional[str] = None, learn: bool = False, max_iterations: int = 5, 
        comment_prefix: str = '//', memory_db_path: Optional[str] = None
    ) -> bool:
        """
        Prepares the React tool for usage.
        - Clears internal state.
        - Loads or initializes the DB data.
        - Configures learn mode, iteration limit, and comment prefix.
        - Sets _is_ready if successful.

        Args:
            db_path: Path to database for traditional key-based retrieval
            learn: Whether to learn from successful fixes
            max_iterations: Maximum number of iterations to attempt
            comment_prefix: Comment prefix for the target language
            memory_db_path: Path to database for semantic memory retrieval

        Returns:
            True if setup is successful, False otherwise (and sets error_message).
        """
        self.last_code = ''
        self._log.clear()
        self._learn_mode = learn
        self._max_iterations = max_iterations
        self._lang_prefix = comment_prefix
        self._db_path = db_path

        # Initialize the memory system if a path is provided
        if memory_db_path:
            try:
                self._memory = FewShotMemory(db_path=memory_db_path)
            except Exception as e:
                self.error_message = f'Failed to initialize memory system: {e}'
                self._is_ready = False
                return False
        
        if self._db_path:
            if os.path.exists(self._db_path):
                try:
                    self._load_db()
                    # Initialize memory from traditional DB if memory is enabled but empty
                    if self._memory and not self._memory.memories and self._db:
                        self._initialize_memory_from_db()
                except Exception as e:
                    self.error_message = f'Failed to load DB: {e}'
                    self._is_ready = False
                    return False
            else:
                if self._learn_mode:
                    self._db = {}
                    try:
                        self._save_db()
                    except Exception as e:
                        self.error_message = f'Failed to create DB: {e}'
                        self._is_ready = False
                        return False
                else:
                    self.error_message = 'Database file not found and learn mode is disabled.'
                    self._is_ready = False
                    return False
        else:
            self._db = {}

        self._is_ready = True
        return True

    def _load_db(self) -> None:
        """
        Reads the YAML database file from `_db_path` into `_db`.
        """
        if not os.path.exists(self._db_path):
            self._db = {}
            return

        yaml_loader = YAML(typ='safe')
        with open(self._db_path, 'r', encoding='utf-8') as f:
            data = yaml_loader.load(f)
            if data is None:
                data = {}
            # Ensure the data is a mapping.
            assert isinstance(data, dict), 'Database file must contain a mapping'
            self._db = data

    def _save_db(self) -> None:
        """
        Writes `_db` back to disk (only if learn mode is enabled) using
        literal block style for multiline strings.
        """
        if self._learn_mode and self._db_path:
            yaml_writer = YAML()
            # Configure indentation for better readability.
            yaml_writer.indent(mapping=2, sequence=4, offset=2)
            # Process _db to wrap multiline strings.
            processed_db = process_multiline_strings(self._db)
            with open(self._db_path, 'w', encoding='utf-8') as f:
                yaml_writer.dump(processed_db, f)

    def _add_error_example(self, error_type: str, fix_question: str, fix_answer: str) -> None:
        """
        Updates `_db` with a new error example if not already present.
        Immediately saves if learning mode is enabled.
        """
        if error_type not in self._db:
            self._db[error_type] = {'fix_question': fix_question, 'fix_answer': fix_answer}
            if self._learn_mode:
                self._save_db()

    def _initialize_memory_from_db(self) -> None:
        """
        Convert examples from the traditional DB to memory system
        """
        if not self._memory:
            return
            
        for error_type, data in self._db.items():
            self._memory.add(
                original_code=data["fix_question"],
                fixed_code=data["fix_answer"],
                errors=[error_type]
            )

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
          4. Uses semantic memory system to find similar examples, if available.
          5. Inserts a multi-line comment (with all diagnostic details) into the code.
          6. On the first iteration, passes only a delta (a few lines around the error)
             to fix_callback. If that fix does not work, applies the returned patch to the
             full code. Subsequent iterations pass the full code.
          7. Calls fix_callback to obtain a proposed fix.
          8. Checks if progress is made or if iteration limit is reached.
          9. Optionally learns new error examples if learning is enabled.
          10. Returns the text that is error–free or an empty string if unable to fix.
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
            fix_example = self._db.get(error_type, {'fix_question': '', 'fix_answer': ''})
            assert isinstance(fix_example, dict), f'Corrupt llm_wrap DB {self._db_path}'

            # Try to find similar examples using the memory system
            if self._memory:
                memories = self._memory.find(
                    current_text,
                    errors=[d.msg for d in diagnostics]
                )
                
                # If we found similar examples, add them to fix_example
                if memories:
                    top_match = memories[0]
                    fix_example = {
                        "fix_question": top_match.faulty_code,
                        "fix_answer": top_match.fixed_code,
                        "error_type": top_match.error_type,
                        "similar_examples": [Memory.to_dict(m) for m in memories[:3]]
                    }
                    iteration_log['memory_match'] = Memory.to_dict(top_match)

            if iteration == 1:
                # Use a delta: only a few lines around the first error.
                delta, start_line, end_line = self._get_delta(current_text, diagnostics[0].loc)
                # Compute relative error location in the delta.
                # relative_loc = diagnostics[0].loc - start_line + 1
                try:
                    # annotated = insert_comment(delta, diagnostics[0].to_str(), self._lang_prefix, relative_loc)
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
                    # annotated = insert_comment(current_text, diagnostics[0].to_str(), self._lang_prefix, diagnostics[0].loc)
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
                    # Add to traditional database
                    self._add_error_example(error_type, fix_question, fix_answer)
                    
                    # Also add to memory system for semantic similarity retrieval
                    if self._memory:
                        self._memory.add(
                            original_code=fix_question,
                            fixed_code=fix_answer,
                            errors=[diagnostics[0].msg]
                        )
                self.last_code = new_text
                return new_text
            else:
                new_error_type = new_diagnostics[0].error
                if new_error_type != error_type and self._learn_mode:
                    self._add_error_example(error_type, fix_question, fix_answer)
                    
                    # Also add to memory for different error types
                    if self._memory:
                        self._memory.add(
                            original_code=fix_question,
                            fixed_code=fix_answer,
                            errors=[diagnostics[0].msg]
                        )
                current_text = new_text

        self.last_code = current_text
        return ''

    def get_log(self) -> List[Dict]:
        """
        Returns the log of the iterations.
        """
        return self._log