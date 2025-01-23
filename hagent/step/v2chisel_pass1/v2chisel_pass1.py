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
        """
        1) Reads the input data from YAML (via super().setup()).
        2) Initializes the LLM with prompt1.yaml.
        """
        super().setup()  # base Step loads self.input_data

        # Check for 'llm' in YAML
        if 'llm' not in self.input_data:
            self.error("Missing 'llm' section in input YAML")

        # Load main prompt (prompt1.yaml) for generating updated Chisel
        prompt_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'prompt1.yaml')
        if not os.path.exists(prompt_file):
            self.error(f"Prompt file not found: {prompt_file}")

        self.prompt1_template = LLM_template(prompt_file)

        # Initialize the LLM
        llm_args = self.input_data['llm']
        self.lw = LLM_wrap()
        self.lw.from_dict(name='v2chisel_pass1', conf_dict=llm_args, prompt=self.prompt1_template)

        self.setup_called = True

    def run(self, data):
        """
        Main pass logic:
          1) Gather verilog_original, verilog_fixed, chisel_original from YAML.
          2) Compute a diff between verilog_original & verilog_fixed (placeholder).
          3) Prompt the LLM to produce 'chisel_changed'.
          4) Call chisel2v to confirm we can generate valid Verilog from 'chisel_changed'.
          5) If invalid, use prompt2.yaml and re-try (placeholder).
          6) Write final results into the output data in 'chisel_pass1' field.
        """
        # Step 1: Gather required fields
        verilog_original = data.get('verilog_original', '')
        verilog_fixed    = data.get('verilog_fixed', '')
        chisel_original  = data.get('chisel_original', '')

        print("[INFO] v2chisel_pass1: Comparing verilog_original vs. verilog_fixed to derive updates.")
        if not verilog_original or not verilog_fixed:
            print("[WARN] verilog_original or verilog_fixed is empty. LLM might not know what to change.")

        # Step 2: Compute a naive diff
        verilog_diff_list = list(difflib.unified_diff(
            verilog_original.splitlines(),
            verilog_fixed.splitlines(),
            lineterm=''
        ))
        verilog_diff_text = "\n".join(verilog_diff_list)
        print("[DEBUG] Diff:\n", verilog_diff_text)

        # Step 3: Prompt the LLM
        prompt_dict = {
            'chisel_original': chisel_original,
            'verilog_diff':    verilog_diff_text
        }
        response_list = self.lw.inference(prompt_dict, n=1)
        if not response_list:
            self.error("LLM returned an empty response from prompt1.yaml")

        chisel_changed = response_list[0]
        chisel_changed = self._strip_markdown_fences(chisel_changed)

        print("[INFO] LLM produced an updated Chisel snippet. Checking if it's valid...")

        # Step 4: Call chisel2v to confirm validity
        valid_first, verilog_candidate = self._run_chisel2v(chisel_changed)
        if not valid_first:
            print("[WARN] The generated Chisel code failed to produce valid Verilog. Trying prompt2.yaml...")

            # Step 5: Retry with prompt2.yaml (placeholder)
            prompt2_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'prompt2.yaml')
            if os.path.exists(prompt2_file):
                prompt2_template = LLM_template(prompt2_file)
                self.lw.from_dict(name='v2chisel_pass1_retry', conf_dict=data['llm'], prompt=prompt2_template)

                retry_response_list = self.lw.inference(prompt_dict, n=1)
                if retry_response_list:
                    chisel_changed = retry_response_list[0]
                    chisel_changed = self._strip_markdown_fences(chisel_changed)
                    valid_second, verilog_candidate = self._run_chisel2v(chisel_changed)
                    if not valid_second:
                        print("[ERROR] Even after prompt2, code is invalid. We'll store it anyway.")
                else:
                    print("[ERROR] No response from prompt2.yaml either; storing first attempt.")
            else:
                print("[WARN] No prompt2.yaml found; storing first attempt as is.")

        # Step 6: Write results back to the YAML dictionary
        result = data.copy()
        result['chisel_pass1'] = {
            'chisel_changed': chisel_changed,
            'verilog_candidate': verilog_candidate,
            # If the final attempt was valid or not
            # (We can’t know which attempt if we never set flags, but let's say we store a boolean.)
            'was_valid': (verilog_candidate is not None)
        }

        return result

    # ---------------------------------------------------------------------
    # Internal helper to remove triple backticks from the LLM response
    # ---------------------------------------------------------------------
    def _strip_markdown_fences(self, code_str: str) -> str:
        """Remove ```scala, ```verilog, or generic triple backticks from code_str."""
        import re
        code_str = re.sub(r'```[a-zA-Z]*', '', code_str)
        code_str = code_str.replace('```', '').strip()
        return code_str

    # ---------------------------------------------------------------------
    # Method calling the Chisel2v tool
    # ---------------------------------------------------------------------
    def _run_chisel2v(self, chisel_code: str):
        """
        Attempt to generate Verilog from the Chisel code using the real chisel2v.py tool.
        Returns (is_valid, verilog_string or None).
        """
        if not chisel_code.strip():
            return (False, None)

        c2v = Chisel2v()
        # 1) Try to set up (check sbt)
        success = c2v.setup()
        if not success:
            print(f"[ERROR] chisel2v setup failed: {c2v.error_message}")
            return (False, None)

        # 2) Extract the top-level module name or use fallback "MyModule"
        module_name = self._find_chisel_classname(chisel_code)
        if not module_name:
            module_name = "MyModule"

        # 3) Call generate_verilog
        try:
            verilog_output = c2v.generate_verilog(chisel_code, module_name)
            # Check for a minimal "module" text in output
            if "module" not in verilog_output:
                return (False, None)
            return (True, verilog_output)
        except RuntimeError as e:
            print(f"[ERROR] chisel2v error: {str(e)}")
            return (False, None)

    def _find_chisel_classname(self, chisel_code: str) -> str:
        """
        Tries to parse something like 'class MyTop extends Module' from the code.
        Returns 'MyTop' or empty string if not found.
        """
        regex = r'class\s+([A-Za-z0-9_]+)\s+extends\s+Module'
        match = re.search(regex, chisel_code)
        if match:
            return match.group(1)
        return ""

if __name__ == '__main__':  # pragma: no cover
    step = V2ChiselPass1()
    step.parse_arguments()
    step.setup()
    step.step()