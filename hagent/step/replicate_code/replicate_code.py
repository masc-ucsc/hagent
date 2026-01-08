#!/usr/bin/env python3
# See LICENSE for details

import json
import os
import sys
import time
from hagent.core.step import Step
from hagent.core.llm_wrap import LLM_wrap
from hagent.tool.compile_slang import Compile_slang
from hagent.tool.equiv_check import Equiv_check
from hagent.tool.extract_code import Extract_code_verilog
from hagent.inou.path_manager import PathManager


class Replicate_code(Step):
    def setup(self):
        super().setup()  # superclass

        # Hardcoded configuration (no YAML config section)
        self.MAX_COMPILE_ITERATIONS = 2
        self.MAX_LEC_ITERATIONS = 1
        self.MAX_TOTAL_LLM_CALLS = 5

        # Initialize Verilog extractor
        self.verilog_extractor = Extract_code_verilog()

        # Initialize compiler for syntax checking
        self.compiler = Compile_slang()
        if not self.compiler.setup():
            print(f'WARNING: Compile_slang not available: {self.compiler.error_message}')
            self.compiler = None

        # Load expert fix examples database
        self.expert_examples = self._load_expert_examples()

        # Budget tracking
        self.llm_call_count = 0

        # Initialize LLM wrapper (existing code)
        self.setup_called = True
        conf_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'dummy_config.yaml')

        self.lw = LLM_wrap(
            name='replicate_code', log_file='replicate_code.log', conf_file=conf_file, overwrite_conf=self.input_data
        )

        if self.lw.last_error:
            raise ValueError(self.lw.last_error)

    def check_lec(self, data) -> list[str]:
        try:
            original_code = data['code_content']
            optimized_codes = data['optimized']  # this is a list
            top_name = data['top_name']
        except Exception as e:
            print(f'Error: Missing field in data. {e}')
            sys.exit(1)

        # Instantiate the equivalence checker
        checker = Equiv_check()

        # Setup: check if Yosys is accessible
        ok = checker.setup()
        if not ok:
            print(f'Equiv_check setup failed: {checker.get_error()}')
            sys.exit(1)

        # run equiv check:
        result = []  # this will store, in the yaml, the optimized codes which pass lec
        for optimized_code in optimized_codes:
            try:
                # print(f'!!!!original_code: {original_code}')
                # print(f'!!!!optimized_code: {optimized_code}')

                lec_result = checker.check_equivalence(original_code, optimized_code, top_name)
            except Exception as e:
                print(f'Error: equivalence failed. {e}')
                lec_result = False  # Continue with other codes instead of exiting
            # Interpret the result and decide lec value
            if lec_result is True:
                print('~~~~LEC passed.~~~~')
                result.append(optimized_code)
            elif lec_result is False:
                print('~~~~LEC FAILED!~~~~')
            else:
                print()
                print('Equivalence check inconclusive.')
                print(f'Error message: {checker.get_error()}')
        if isinstance(result, list) and len(result) > 0:
            print(f'SUCCESS: {len(result)} lec passing result obtained.')
        else:
            print('WARNING: No lec passing result obtained.')

        return result

    def run(self, data):
        original_code = data['code_content']
        top_name = data['top_name']

        # Phase 1: Initial generation with categorization
        initial_results = self._generate_initial_variants(original_code, top_name)

        # Phase 2: Compilation feedback
        if initial_results['compile_failed']:
            print(f'\n[Phase 2] Running compilation feedback on {len(initial_results["compile_failed"])} variants...')
            compile_refined = self._compilation_feedback_loop(original_code, top_name, initial_results['compile_failed'])
            initial_results['passing'].extend(compile_refined['passing'])
            initial_results['lec_failed'].extend(compile_refined['lec_failed'])

        # Phase 3: LEC feedback
        if initial_results['lec_failed']:
            print(f'\n[Phase 3] Running LEC feedback on {len(initial_results["lec_failed"])} variants...')
            lec_refined = self._lec_feedback_loop(original_code, top_name, initial_results['lec_failed'])
            initial_results['passing'].extend(lec_refined['passing'])

        # Format output (maintain backward compatibility)
        result = data.copy()
        result['optimized_equivalent'] = initial_results['passing']

        # Save to files (existing behavior)
        x = 3
        # get the optimized code from result and save it in output directory
        output_dir = PathManager().get_cache_dir()
        for code in initial_results['passing']:
            filename = os.path.join(output_dir, f'option_{x}.v')
            x += 1
            os.makedirs(os.path.dirname(filename), exist_ok=True)
            with open(filename, 'w') as f:
                f.write(code)

        # Print final summary
        if initial_results['passing']:
            print(f'\nSUCCESS: {len(initial_results["passing"])} LEC-passing variants obtained.')
            print(f'Total LLM calls used: {self.llm_call_count}/{self.MAX_TOTAL_LLM_CALLS}')
        else:
            print('\nWARNING: No LEC-passing variants obtained after feedback loops.')
            print(f'Total LLM calls used: {self.llm_call_count}/{self.MAX_TOTAL_LLM_CALLS}')

        return result

    def _generate_initial_variants(self, original_code: str, top_name: str) -> dict:
        """
        Generate initial variants and categorize by failure type.

        Returns:
            {
                'passing': [code1, code2, ...],
                'compile_failed': [{'code': str, 'error': str}, ...],
                'lec_failed': [{'code': str, 'error': str, 'counterexample': str}, ...]
            }
        """
        print('[Phase 1] Generating initial variants...')

        # Call LLM (existing behavior, 1 call)
        try:
            responses = self.lw.inference({'code_content': original_code}, 'replicate_code_prompt1', n=2)
            self.llm_call_count = 1
        except Exception as e:
            print(f'ERROR: Initial LLM generation failed: {e}')
            return {'passing': [], 'compile_failed': [], 'lec_failed': []}

        results = {'passing': [], 'compile_failed': [], 'lec_failed': []}

        # Extract and categorize each variant
        for markdown in responses:
            codes = self.verilog_extractor.parse(markdown)
            for code in codes:
                if not code or self._is_identical(code, original_code):
                    continue

                # Compile check before LEC
                compile_ok, compile_error = self._check_compilation(code)
                if not compile_ok:
                    results['compile_failed'].append({'code': code, 'error': compile_error})
                    print(f'  Variant failed compilation: {compile_error[:100]}...')
                    continue

                # LEC check
                lec_ok, lec_error, lec_cex = self._check_lec_detailed(original_code, code, top_name)

                if lec_ok:
                    results['passing'].append(code)
                    print('  Variant passed LEC!')
                else:
                    results['lec_failed'].append({'code': code, 'error': lec_error, 'counterexample': lec_cex})
                    print(f'  Variant failed LEC: {lec_error[:100]}...')

        print(
            f'[Phase 1] Results: {len(results["passing"])} passing, '
            f'{len(results["compile_failed"])} compile failed, '
            f'{len(results["lec_failed"])} LEC failed'
        )

        return results

    def _compilation_feedback_loop(self, original_code: str, top_name: str, failed_variants: list) -> dict:
        """
        Iteratively refine variants that failed compilation.

        Returns:
            {'passing': [...], 'lec_failed': [...]}
        """
        results = {'passing': [], 'lec_failed': []}

        for variant_info in failed_variants:
            current_code = variant_info['code']
            current_error = variant_info['error']

            for iteration in range(1, self.MAX_COMPILE_ITERATIONS + 1):
                # Budget check
                if self.llm_call_count >= self.MAX_TOTAL_LLM_CALLS:
                    print('  WARNING: Hit LLM call budget limit')
                    break

                print(f'  Compile feedback iteration {iteration}...')

                # Call LLM with compilation feedback
                refined_code = self._refine_with_compile_feedback(original_code, current_code, current_error)

                if not refined_code:
                    print('    LLM returned empty, breaking')
                    break

                # Check compilation
                compile_ok, compile_error = self._check_compilation(refined_code)
                if not compile_ok:
                    print('    Still has compile errors, retrying...')
                    current_code = refined_code
                    current_error = compile_error
                    continue

                print('    Compilation passed!')

                # Check LEC
                lec_ok, lec_error, lec_cex = self._check_lec_detailed(original_code, refined_code, top_name)

                if lec_ok:
                    print('    LEC passed! Compile feedback succeeded.')
                    results['passing'].append(refined_code)
                else:
                    print('    LEC failed, adding to LEC feedback pool')
                    results['lec_failed'].append({'code': refined_code, 'error': lec_error, 'counterexample': lec_cex})

                break  # Move to next variant

        return results

    def _lec_feedback_loop(self, original_code: str, top_name: str, failed_variants: list) -> dict:
        """
        Iteratively refine variants that failed LEC.

        Returns:
            {'passing': [...]}
        """
        results = {'passing': []}

        for variant_info in failed_variants:
            # Budget check
            if self.llm_call_count >= self.MAX_TOTAL_LLM_CALLS:
                print('  WARNING: Hit LLM call budget limit')
                break

            print('  LEC feedback iteration 1...')

            # Call LLM with LEC feedback
            refined_code = self._refine_with_lec_feedback(
                original_code, variant_info['code'], variant_info['error'], variant_info['counterexample']
            )

            if not refined_code:
                print('    LLM returned empty, continuing')
                continue

            # Compilation check (must still compile)
            compile_ok, compile_error = self._check_compilation(refined_code)
            if not compile_ok:
                print(f'    Introduced compile error, skipping: {compile_error[:80]}')
                continue

            # LEC check
            lec_ok, _, _ = self._check_lec_detailed(original_code, refined_code, top_name)

            if lec_ok:
                print('    LEC passed! LEC feedback succeeded.')
                results['passing'].append(refined_code)
            else:
                print('    LEC still failing')

        return results

    def _refine_with_compile_feedback(self, original_code: str, failed_code: str, error: str) -> str:
        """
        Call LLM with compilation error feedback and human expert guidance.

        Returns:
            Refined Verilog code string, or empty string on failure
        """
        # Get relevant expert examples for compilation errors
        human_guidance = self._get_relevant_examples('compile', error)

        prompt_dict = {
            'original_code': original_code,
            'failed_code': failed_code,
            'compile_error': error,
            'human_guidance': human_guidance,
        }

        try:
            responses = self.lw.inference(prompt_dict, 'replicate_code_compile_feedback', n=1, max_history=0)
            self.llm_call_count += 1

            if not responses:
                return ''

            # Extract first valid code block
            for markdown in responses:
                codes = self.verilog_extractor.parse(markdown)
                if codes and codes[0]:
                    return codes[0]

            return ''

        except Exception as e:
            print(f'ERROR: Compile feedback LLM call failed: {e}')
            return ''

    def _refine_with_lec_feedback(self, original_code: str, failed_code: str, error: str, cex: str) -> str:
        """
        Call LLM with LEC error, counterexample, and human expert guidance.

        Returns:
            Refined Verilog code string, or empty string on failure
        """
        # Get relevant expert examples for LEC errors
        human_guidance = self._get_relevant_examples('lec', error)

        prompt_dict = {
            'original_code': original_code,
            'failed_code': failed_code,
            'lec_error': error or 'LEC equivalence check failed',
            'counterexample': cex or 'No counterexample available',
            'human_guidance': human_guidance,
        }

        try:
            responses = self.lw.inference(prompt_dict, 'replicate_code_lec_feedback', n=1, max_history=0)
            self.llm_call_count += 1

            if not responses:
                return ''

            # Extract first valid code block
            for markdown in responses:
                codes = self.verilog_extractor.parse(markdown)
                if codes and codes[0]:
                    return codes[0]

            return ''

        except Exception as e:
            print(f'ERROR: LEC feedback LLM call failed: {e}')
            return ''

    def _check_compilation(self, code: str) -> tuple[bool, str]:
        """
        Check Verilog compilation using Compile_slang.

        Returns:
            (is_valid, error_message)
        """
        if not self.compiler:
            return (False, 'Compiler unavailable')

        compiler = Compile_slang()
        if not compiler.setup():
            return (False, 'Slang setup failed')

        if not compiler.add_inline(code):
            return (False, compiler.error_message)

        errors = compiler.get_errors()
        if errors:
            error_text = '\n'.join([e.msg for e in errors])
            return (False, error_text)

        return (True, '')

    def _check_lec_detailed(self, original: str, optimized: str, top_name: str) -> tuple[bool, str, str]:
        """
        Check LEC and return detailed error information.

        Returns:
            (is_equivalent, error_message, counterexample)
        """
        checker = Equiv_check()
        if not checker.setup():
            error = checker.get_error() or 'Equiv_check setup failed'
            return (False, error, '')

        try:
            result = checker.check_equivalence(original, optimized, top_name)

            if result is True:
                return (True, '', '')
            elif result is False:
                error = checker.get_error() or 'LEC mismatch'
                cex = checker.get_counterexample() or ''
                return (False, error, cex)
            else:  # None - inconclusive
                error = checker.get_error() or 'LEC inconclusive'
                return (False, error, '')

        except Exception as e:
            return (False, str(e), '')

    def _is_identical(self, code1: str, code2: str) -> bool:
        """Check if two code snippets are identical (ignoring whitespace)"""
        normalized1 = ' '.join(code1.split())
        normalized2 = ' '.join(code2.split())
        return normalized1 == normalized2

    def _load_expert_examples(self) -> dict:
        """Load expert fix examples from JSON database"""
        examples_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'expert_fix_examples.json')

        try:
            if os.path.exists(examples_file):
                with open(examples_file) as f:
                    return json.load(f)
            else:
                print(f'WARNING: Expert examples file not found: {examples_file}')
                return {'compile_errors': {}, 'lec_errors': {}}
        except Exception as e:
            print(f'WARNING: Failed to load expert examples: {e}')
            return {'compile_errors': {}, 'lec_errors': {}}

    def _get_relevant_examples(self, example_type: str, error_message: str) -> str:
        """
        Get relevant expert examples using exact error tag matching (RAG approach).

        Args:
            example_type: 'compile' or 'lec'
            error_message: The error message to match against

        Returns:
            Formatted string with human expert guidance and demonstrations
        """
        if not hasattr(self, 'expert_examples') or not self.expert_examples:
            return ''

        # Use exact match on error tags for retrieval
        key = 'compile_errors' if example_type == 'compile' else 'lec_errors'
        error_db = self.expert_examples.get(key, {})

        if not error_db:
            return ''

        # Try exact match on known error tags
        matched_examples = []
        error_lower = error_message.lower()

        for error_tag, entry in error_db.items():
            # Check if error tag or compiler log pattern appears in the error message
            if error_tag.replace('_', ' ') in error_lower or entry.get('compiler_log_pattern', '').lower() in error_lower:
                matched_examples.append(entry)

        if not matched_examples:
            # No exact match found, return empty (could be extended with fuzzy matching later)
            return ''

        # Format human expert guidance
        formatted = 'Human Expert Guidance:\n\n'
        for entry in matched_examples[:3]:  # Limit to top 3 matches
            if example_type == 'compile':
                formatted += f'Compiler Logs: {entry.get("compiler_log_pattern", "")}\n'
                formatted += f'Error cause: {entry.get("cause", "")}\n\n'
                formatted += f'Verilog rule: {entry.get("rule", "")}\n\n'
                formatted += f'Fix strategy: {entry.get("fix_strategy", "")}\n\n'
                if 'demo_bad' in entry and 'demo_good' in entry:
                    formatted += f'Example (before fix):\n```verilog\n{entry["demo_bad"]}\n```\n'
                    formatted += f'Example (after fix):\n```verilog\n{entry["demo_good"]}\n```\n\n'
            else:  # LEC
                raise NotImplementedError

        return formatted


if __name__ == '__main__':  # pragma: no cover
    start_time = time.time()
    rep_step = Replicate_code()
    rep_step.parse_arguments()  # or rep_step.set_io(...)
    end_time = time.time()
    print(f'\nTIME: parse duration: {(end_time - start_time):.4f} seconds\n')
    start_time = time.time()
    rep_step.setup()
    end_time = time.time()
    print(f'\nTIME: setup duration: {(end_time - start_time):.4f} seconds\n')
    start_time = time.time()
    # result =
    rep_step.step()
    end_time = time.time()
    print(f'\nTIME: step duration: {(end_time - start_time):.4f} seconds\n')

    # result = wrap_literals(result)
