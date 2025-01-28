#!/usr/bin/env python3
# See LICENSE for details

import os
import re
import difflib
from hagent.core.step import Step
from hagent.core.llm_template import LLM_template
from hagent.core.llm_wrap import LLM_wrap

from hagent.tool.chisel2v import Chisel2v


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

    def run(self, data):
        verilog_original = data.get('verilog_original', '')
        verilog_fixed = data.get('verilog_fixed', '')
        chisel_original = data.get('chisel_original', '')

        # Compute a naive diff for verilog
        verilog_diff_list = list(difflib.unified_diff(verilog_original.splitlines(), verilog_fixed.splitlines(), lineterm=''))
        verilog_diff_text = '\n'.join(verilog_diff_list)

        max_iterations = 5
        was_valid = False
        chisel_changed_final = None
        verilog_candidate_final = None
        last_error_msg = ''

        for attempt in range(1, max_iterations + 1):
            # For attempt >= 2 => use prompt2.yaml if it exists
            if attempt > 1:
                prompt2_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'prompt2.yaml')
                if os.path.exists(prompt2_file):
                    prompt2_template = LLM_template(prompt2_file)
                    self.lw.from_dict(name='v2chisel_pass1_retry', conf_dict=data['llm'], prompt=prompt2_template)
                # else: (no prompt2, keep using prompt1)

            # Build dictionary for the LLM
            prompt_dict = {
                'verilog_original': verilog_original,
                'verilog_fixed': verilog_fixed,
                'chisel_original': chisel_original,
                'verilog_diff': verilog_diff_text,
                'error_msg': last_error_msg,
            }

            # === PRINT the LLM QUERY ===
            # We can manually format the template to see what the final text is
            formatted_prompt = self.lw.chat_template.format(prompt_dict)
            print('\n================ LLM QUERY (attempt {}) ================'.format(attempt))
            # 'formatted_prompt' is a list of role/content dicts
            for chunk in formatted_prompt:
                print(f"Role: {chunk['role']}")
                print('Content:')
                print(chunk['content'])
                print('------------------------------------------------')

            # === CALL the LLM ===
            response_list = self.lw.inference(prompt_dict, n=1)

            if not response_list:
                print('\n=== LLM RESPONSE: EMPTY ===\n')
                last_error_msg = 'LLM gave empty response'
                continue

            # === PRINT the LLM RESPONSE ===
            print('\n================ LLM RESPONSE ================')
            print(response_list[0])
            print('==============================================')

            # Now do minimal validation
            chisel_changed = self._strip_markdown_fences(response_list[0])
            is_valid, verilog_candidate, error_msg = self._run_chisel2v(chisel_changed)
            if is_valid:
                chisel_changed_final = chisel_changed
                verilog_candidate_final = verilog_candidate
                was_valid = True
                break
            else:
                last_error_msg = error_msg or 'Unknown chisel2v error'

        # Construct final result
        if not was_valid and chisel_changed_final is None:
            chisel_changed_final = 'No valid snippet generated.'

        result = data.copy()
        result['chisel_pass1'] = {
            'chisel_changed': chisel_changed_final,
            'verilog_candidate': verilog_candidate_final,
            'was_valid': was_valid,
        }
        return result

    def _strip_markdown_fences(self, code_str: str) -> str:
        code_str = re.sub(r'```[a-zA-Z]*', '', code_str)
        code_str = code_str.replace('```', '').strip()
        return code_str

    def _run_chisel2v(self, chisel_code: str):
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


if __name__ == '__main__':  # pragma: no cover
    step = V2ChiselPass1()
    step.parse_arguments()
    step.setup()
    step.step()
