"""
ChiselDiffGenerator component for v2chisel_batch.

This component handles LLM-based generation of Chisel diffs from Verilog diffs and hints.
Provides a clean interface for calling the LLM with structured prompts.
"""

from typing import Dict, Any
from hagent.core.llm_wrap import LLM_wrap


class ChiselDiffGenerator:
    """
    Handles LLM calls to generate Chisel diffs from Verilog diffs and hints.

    This component:
    1. Takes Verilog diff + Chisel hints as input
    2. Constructs structured prompt for LLM
    3. Calls LLM to generate Chisel diff
    4. Returns formatted Chisel diff ready for application

    Uses LLM_wrap for API calls and template-based prompt formatting.
    """

    def __init__(self, llm_config_file: str, llm_name: str, debug: bool = True):
        """
        Initialize ChiselDiffGenerator.

        Args:
            llm_config_file: Path to LLM configuration YAML file
            llm_name: Name of LLM config section (e.g., 'openai_gpt4', 'claude')
            debug: Enable debug output
        """
        self.llm_config_file = llm_config_file
        self.llm_name = llm_name
        self.debug = debug

        # Initialize LLM wrapper (lazy initialization on first use)
        self.llm_wrap = None

    def _init_llm(self) -> bool:
        """
        Initialize LLM wrapper on first use.

        Returns:
            bool: True if initialization successful
        """
        if self.llm_wrap is not None:
            return True

        try:
            self.llm_wrap = LLM_wrap(self.llm_name, self.llm_config_file)

            if self.llm_wrap.last_error:
                if self.debug:
                    print(f'❌ [LLM] Failed to initialize LLM: {self.llm_wrap.last_error}')
                return False

            if self.debug:
                print(f'✅ [LLM] Initialized LLM wrapper: {self.llm_name}')
            return True

        except Exception as e:
            if self.debug:
                print(f'❌ [LLM] Exception initializing LLM: {str(e)}')
            return False

    def generate_chisel_diff(
        self,
        verilog_diff: str,
        chisel_hints: str,
        bug_description: str = '',
        max_retries: int = 3,
        prompt_name: str = 'prompt_initial',
        previous_chisel_diff: str = '',
        error_message: str = '',
        attempt_history: str = '',
    ) -> Dict[str, Any]:
        """
        Generate Chisel diff from Verilog diff using LLM.

        Args:
            verilog_diff: Unified diff of Verilog changes
            chisel_hints: Hints about relevant Chisel files and patterns
            bug_description: Optional description of the bug
            max_retries: Maximum number of retry attempts on failure
            prompt_name: Which prompt to use (prompt_initial, prompt_compile_error, etc.)
            previous_chisel_diff: Previous diff that failed (for retry prompts)
            error_message: Error message from previous attempt (compile_error, lec_error, etc.)
            attempt_history: History of all previous attempts (for prompt_final_attempt)

        Returns:
            Dict with:
                - success: bool
                - chisel_diff: Generated Chisel diff (if successful)
                - error: Error message (if failed)
                - llm_response: Raw LLM response
                - attempts: Number of attempts made
        """
        if not self._init_llm():
            return {'success': False, 'error': 'Failed to initialize LLM', 'chisel_diff': '', 'attempts': 0}

        if self.debug:
            print(f'🤖 [LLM] Generating Chisel diff using prompt: {prompt_name}')

        # Prepare prompt variables based on prompt type
        prompt_vars = {
            'verilog_diff': verilog_diff,
            'chisel_hints': chisel_hints,
            'bug_description': bug_description if bug_description else 'No description provided',
            'previous_chisel_diff': previous_chisel_diff,
            'current_chisel_diff': previous_chisel_diff,
            'compile_error': error_message,
            'lec_error': error_message,
            'attempt_history': attempt_history,
            'ambiguous_lines_info': error_message,
        }

        # Try to get response from LLM with retries
        for attempt in range(1, max_retries + 1):
            try:
                if self.debug:
                    print(f'🔄 [LLM] Attempt {attempt}/{max_retries}...')

                # Call LLM using inference method
                # Use the specified prompt from v2chisel_batch_conf.yaml
                responses = self.llm_wrap.inference(
                    prompt_dict=prompt_vars,
                    prompt_index=prompt_name,  # Use the prompt passed as parameter
                    n=1,
                    max_history=0,
                )

                if responses and len(responses) > 0:
                    llm_response = responses[0]

                    # Extract Chisel diff from response
                    chisel_diff = self._extract_chisel_diff(llm_response)

                    if chisel_diff:
                        if self.debug:
                            print(f'✅ [LLM] Successfully generated Chisel diff on attempt {attempt}')
                            print(f'   Diff length: {len(chisel_diff)} characters')

                        return {
                            'success': True,
                            'chisel_diff': chisel_diff,
                            'llm_response': llm_response,
                            'attempts': attempt,
                            'cost': self.llm_wrap.total_cost,
                            'tokens': self.llm_wrap.total_tokens,
                        }
                    else:
                        if self.debug:
                            print(f'⚠️  [LLM] Attempt {attempt}: No valid Chisel diff found in response')

                else:
                    if self.debug:
                        print(f'⚠️  [LLM] Attempt {attempt}: Empty response from LLM')

            except Exception as e:
                if self.debug:
                    print(f'❌ [LLM] Attempt {attempt} failed with exception: {str(e)}')

                if attempt == max_retries:
                    return {
                        'success': False,
                        'error': f'All {max_retries} attempts failed. Last error: {str(e)}',
                        'chisel_diff': '',
                        'attempts': attempt,
                    }

        # All retries exhausted
        return {
            'success': False,
            'error': f'Failed to generate valid Chisel diff after {max_retries} attempts',
            'chisel_diff': '',
            'attempts': max_retries,
        }

    def _extract_chisel_diff(self, llm_response: str) -> str:
        """
        Extract Chisel diff from LLM response.

        The LLM response may contain explanation text along with the diff.
        This method extracts just the diff portion.

        Args:
            llm_response: Raw response from LLM

        Returns:
            Extracted Chisel diff, or empty string if no valid diff found
        """
        if not llm_response:
            return ''

        # Look for diff markers
        # Common patterns:
        # - ```diff ... ```
        # - --- ... +++ ... @@ ...
        # - Anything between "CHISEL DIFF:" and end

        import re

        # Strategy 1: Look for code blocks with diff
        code_block_pattern = r'```(?:diff|patch)?\s*\n(.*?)\n```'
        matches = re.findall(code_block_pattern, llm_response, re.DOTALL)
        if matches:
            return matches[0].strip()

        # Strategy 2: Look for unified diff format (--- ... +++)
        if '---' in llm_response and '+++' in llm_response:
            # Find the start of the diff
            diff_start = llm_response.find('---')
            if diff_start != -1:
                return llm_response[diff_start:].strip()

        # Strategy 3: Look for explicit markers
        markers = ['CHISEL DIFF:', 'Chisel diff:', 'chisel diff:']
        for marker in markers:
            if marker in llm_response:
                marker_pos = llm_response.find(marker)
                return llm_response[marker_pos + len(marker) :].strip()

        # Strategy 4: If response looks like a diff (contains @@), return as-is
        if '@@' in llm_response and ('---' in llm_response or '+++' in llm_response):
            return llm_response.strip()

        # No diff pattern found - return empty
        if self.debug:
            print('⚠️  [LLM] Could not extract diff from LLM response')
            print(f'   Response preview: {llm_response[:200]}...')

        return ''

    def get_stats(self) -> Dict[str, Any]:
        """
        Get LLM usage statistics.

        Returns:
            Dict with cost, tokens, and timing information
        """
        if self.llm_wrap is None:
            return {'cost': 0, 'tokens': 0, 'time_ms': 0, 'calls': 0}

        return {
            'cost': self.llm_wrap.total_cost,
            'tokens': self.llm_wrap.total_tokens,
            'time_ms': self.llm_wrap.total_time_ms,
            'calls': len(self.llm_wrap.responses),
        }
