#!/usr/bin/env python3
# See LICENSE for details

import os
import re
import difflib
from hagent.core.step import Step
from hagent.core.llm_template import LLM_template
from hagent.core.llm_wrap import LLM_wrap

from hagent.tool.chisel2v import Chisel2v
from hagent.tool.chisel_diff_applier import ChiselDiffApplier

from hagent.tool.extract_verilog_diff_keywords import FuzzyGrepFilter
from hagent.tool.fuzzy_grep import Fuzzy_grep
import tempfile


class V2ChiselPass1(Step):
    def setup(self):
        super().setup()

        if 'llm' not in self.input_data:
            self.error("Missing 'llm' section in input YAML")

        # Load main prompt (prompt1.yaml)
        prompt_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'prompt1.yaml')
        if not os.path.exists(prompt_file):
            self.error(f'Prompt file not found: {prompt_file}')

        self.prompt1_template = LLM_template(prompt_file)
        llm_args = self.input_data['llm']

        self.lw = LLM_wrap()
        self.lw.from_dict(name='v2chisel_pass1', conf_dict=llm_args, prompt=self.prompt1_template)

        self.setup_called = True

    def _generate_diff(self, old_code: str, new_code: str) -> str:
        """
        Generate a unified diff string comparing old_code vs. new_code.
        """
        old_lines = old_code.splitlines()
        new_lines = new_code.splitlines()
        diff_lines = difflib.unified_diff(
            old_lines,
            new_lines,
            fromfile='verilog_original.v',
            tofile='verilog_fixed.v',
            lineterm=''
        )
        return '\n'.join(diff_lines)

    def _extract_chisel_subset(self, chisel_code: str, verilog_diff: str, threshold_override: int = None) -> str:
        """
        Extract candidate hint lines from the Chisel code.
        Instead of using FilterLines, this function:
          1. Extracts keywords from the Verilog diff using FuzzyGrepFilter.
          2. Uses Fuzzy_grep to search for these keywords in the Chisel code.
        Returns the matching hint lines as a string, with "->" marking central matches.
        """ 
        # Step 1: Extract keywords from the Verilog diff.
        keywords = FuzzyGrepFilter.extract_keywords_from_diff(verilog_diff)
        print("------------------------------------------------")
        print("Extracted keywords from verilog diff:")
        print(keywords)
        print("------------------------------------------------")

        # Step 3: Use Fuzzy_grep to search for these keywords in the Chisel code.
        fg = Fuzzy_grep()
        if not fg.setup("chisel"):
            self.error("Fuzzy_grep setup failed: " + fg.error_message)
        
        default_threshold = self.input_data.get("threshold", 40)
        threshold_value = threshold_override if threshold_override is not None else default_threshold
        print("Using fuzzy grep threshold:", threshold_value)
        context_value = self.input_data.get("context", 1)
        print("Using fuzzy grep context:", context_value)

        search_results = fg.search(text=chisel_code, search_terms=keywords, context=context_value, threshold=threshold_value)
        
        hints = ""
        if "text" in search_results:
            matching_lines = []
            for (lineno, line, central) in search_results["text"]:
                marker = "->" if central else "  "
                matching_lines.append(f"{marker}{lineno:4d}: {line}")
            hints = "\n".join(matching_lines)

        print("------------------------------------------------")
        print("Extracted hint lines from chisel code via fuzzy grep:")
        print(hints)
        print("------------------------------------------------")
        
        return hints

    def _strip_markdown_fences(self, code_str: str) -> str:
        """
        Remove markdown code fences (e.g., ```scala or ```) from the string.
        """
        code_str = re.sub(r'```[a-zA-Z]*', '', code_str)
        code_str = code_str.replace('```', '').strip()
        return code_str

    def _fix_formatting(self, code: str) -> str:
        """
        Replace literal escaped newline and tab sequences with actual newline and tab characters.
        """
        fixed = code.replace("\\n", "\n").replace("\\t", "\t")
        return fixed

    def _run_chisel2v(self, chisel_code: str):
        """
        Run the Chisel2v tool to generate Verilog from Chisel code and check its validity.
        """
        if not chisel_code.strip():
            return (False, None, 'Chisel snippet is empty')

        c2v = Chisel2v()
        success = c2v.setup()
        if not success:
            return (False, None, 'chisel2v setup failed: ' + c2v.error_message)

        module_name = self._find_chisel_classname(chisel_code)
        if not module_name:
            module_name = 'MyModule'

        try:
            verilog_out = c2v.generate_verilog(chisel_code, module_name)
            if 'module' not in verilog_out:
                return (False, None, "Generated Verilog missing 'module' keyword.")
            return (True, verilog_out, '')
        except Exception as e:
            return (False, None, str(e))

    def _find_chisel_classname(self, chisel_code: str) -> str:
        m = re.search(r'class\s+([A-Za-z0-9_]+)\s+extends\s+Module', chisel_code)
        return m.group(1) if m else ''

    def run(self, data):
        # Step 1: Generate the Verilog diff.
        verilog_original = data.get('verilog_original', '')
        verilog_fixed = data.get('verilog_fixed', '')
        chisel_original = data.get('chisel_original', '')

        verilog_diff_text = self._generate_diff(verilog_original, verilog_fixed)

        print("************************** Generated Verilog Diff **************************")
        print(verilog_diff_text)
        print("****************************************************")

        # Step 2: Extract the subset (hints) from the original Chisel code.
        default_threshold = self.input_data.get("threshold", 40)
        chisel_subset = self._extract_chisel_subset(chisel_original, verilog_diff_text)
        if not chisel_subset.strip():
            self.error("No hint lines extracted from the Chisel code. Aborting LLM call.")

        max_iterations = 5
        was_valid = False
        chisel_updated_final = None
        verilog_candidate_final = None
        last_error_msg = ''
        generated_diff = ''

        # Use exactly 4 attempts corresponding to the 4 prompts.
        for attempt in range(1, 5):
            if attempt == 1:
                prompt_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'prompt1.yaml')
            elif attempt == 2:
                prompt_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'prompt2.yaml')
            elif attempt == 3:
                prompt_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'prompt3.yaml')
                increased_threshold = default_threshold + 20
                chisel_subset = self._extract_chisel_subset(chisel_original, verilog_diff_text, threshold_override=increased_threshold)
            else:
                prompt_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'prompt4.yaml')
                increased_threshold = default_threshold - 20
                chisel_subset = self._extract_chisel_subset(chisel_original, verilog_diff_text, threshold_override=increased_threshold)

            if not os.path.exists(prompt_file):
                self.error(f'Prompt file not found: {prompt_file}')
            prompt_template = LLM_template(prompt_file)
            if attempt == 1:
                self.lw.from_dict(name='v2chisel_pass1', conf_dict=data['llm'], prompt=prompt_template)
            else:
                self.lw.from_dict(name=f'v2chisel_pass1_retry_{attempt}', conf_dict=data['llm'], prompt=prompt_template)

            prompt_dict = {
                'verilog_original': verilog_original,
                'verilog_fixed': verilog_fixed,
                'chisel_original': chisel_original,
                'chisel_subset': chisel_subset,
                'verilog_diff': verilog_diff_text,
                'error_msg': last_error_msg,
            }

            if attempt > 1:
                prompt_dict['chisel_diff'] = generated_diff

            formatted_prompt = self.lw.chat_template.format(prompt_dict)
            print('\n================ LLM QUERY (attempt {}) ================'.format(attempt))
            for chunk in formatted_prompt:
                print("Role: {}".format(chunk['role']))
                print("Content:")
                print(chunk['content'])
                print("------------------------------------------------")

            response_list = self.lw.inference(prompt_dict, n=1)
            if not response_list:
                print('\n=== LLM RESPONSE: EMPTY ===\n')
                last_error_msg = 'LLM gave empty response'
                continue

            print('\n================ LLM RESPONSE ================')
            print(response_list[0])
            print('==============================================')

            generated_diff = self._strip_markdown_fences(response_list[0])
            applier = ChiselDiffApplier()
            chisel_updated = applier.apply_diff(generated_diff, chisel_original)

            print("===== FINAL CHISEL CODE AFTER DIFF APPLIER (attempt {}) =====".format(attempt))
            print(chisel_updated)

            is_valid, verilog_candidate, error_msg = self._run_chisel2v(chisel_updated)
            if is_valid:
                chisel_updated_final = chisel_updated
                # Fix formatting of the generated Verilog candidate using our new _fix_formatting:
                verilog_candidate_final = self._fix_formatting(verilog_candidate)
                was_valid = True
                break
            else:
                last_error_msg = error_msg or 'Unknown chisel2v error'

        if not was_valid and chisel_updated_final is None:
            chisel_updated_final = 'No valid snippet generated.'

        result = data.copy()
        result['chisel_pass1'] = {
            'chisel_updated': chisel_updated_final,
            'generated_diff': generated_diff,
            'verilog_candidate': verilog_candidate_final,
            'was_valid': was_valid,
        }
        result['verilog_diff'] = verilog_diff_text
        return result


if __name__ == '__main__':  # pragma: no cover
    step = V2ChiselPass1()
    step.parse_arguments()
    step.setup()
    step.step()