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
from hagent.tool.filter_lines import FilterLines
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

    def _extract_chisel_subset(self, chisel_code: str, verilog_diff: str) -> str:
        """
        Extract candidate hint lines from the Chisel code using the FilterLines tool.
        This function writes both the Verilog diff and the Chisel code to temporary files,
        then calls FilterLines.filter_lines() to score and select candidate lines.
        The returned string contains the candidate lines prefixed with "HERE:?" (plus optional context).
        """ 

        # Write the verilog diff to a temporary file.
        with tempfile.NamedTemporaryFile(mode="w+", delete=False, encoding="utf-8") as diff_temp:
            diff_temp.write(verilog_diff)
            diff_temp.flush()
            diff_file = diff_temp.name

        # Write the chisel code to a temporary file.
        with tempfile.NamedTemporaryFile(mode="w+", delete=False, encoding="utf-8") as chisel_temp:
            chisel_temp.write(chisel_code)
            chisel_temp.flush()
            chisel_file = chisel_temp.name

        # Create a FilterLines instance and get the candidate hint lines.
        fl = FilterLines()
        hints = fl.filter_lines(diff_file, chisel_file, context=0)

        print("------------------------------------------------")
        print("Extracted hint lines:")
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
        chisel_subset = self._extract_chisel_subset(chisel_original, verilog_diff_text)

        max_iterations = 5
        was_valid = False
        chisel_updated_final = None
        verilog_candidate_final = None
        last_error_msg = ''
        generated_diff = ''

        for attempt in range(1, max_iterations + 1):
            # For attempts > 1, use prompt2.yaml if available.
            if attempt > 1:
                prompt2_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'prompt2.yaml')
                if os.path.exists(prompt2_file):
                    prompt2_template = LLM_template(prompt2_file)
                    self.lw.from_dict(name='v2chisel_pass1_retry', conf_dict=data['llm'], prompt=prompt2_template)

            # Step 3: Build the prompt dictionary and call the LLM to generate a Chisel diff.
            prompt_dict = {
                'verilog_original': verilog_original,
                'verilog_fixed': verilog_fixed,
                'chisel_original': chisel_original,
                'chisel_subset': chisel_subset,
                'verilog_diff': verilog_diff_text,
                'error_msg': last_error_msg,
            }

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

            # Step 4: Process the response to extract the unified diff.
            generated_diff = self._strip_markdown_fences(response_list[0])

            # Apply the generated diff to the original Chisel code.
            applier = ChiselDiffApplier()
            chisel_updated = applier.apply_diff(generated_diff, chisel_original)

            print("===== FINAL CHISEL CODE AFTER DIFF APPLIER (attempt {}) =====".format(attempt))
            print(chisel_updated)


            # Step 5: Validate the updated Chisel code by compiling it.
            is_valid, verilog_candidate, error_msg = self._run_chisel2v(chisel_updated)
            if is_valid:
                chisel_updated_final = chisel_updated
                verilog_candidate_final = verilog_candidate
                was_valid = True
                break
            else:
                last_error_msg = error_msg or 'Unknown chisel2v error'

        # Step 7: Return the final result.
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
