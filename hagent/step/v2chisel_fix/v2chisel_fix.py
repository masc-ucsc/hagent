#!/usr/bin/env python3
# See LICENSE for details

import os
import re
from hagent.core.step import Step
from hagent.core.llm_template import LLM_template
from hagent.core.llm_wrap import LLM_wrap

from hagent.tool.equiv_check import Equiv_check
from hagent.tool.chisel2v import Chisel2v


class V2ChiselFix(Step):
    def setup(self):
        """
        1) Calls parent setup() to read self.input_data from YAML.
        2) Verifies that 'chisel_pass1' is present in the YAML.
        3) Loads a new prompt (prompt3.yaml) for refining code if LEC fails.
        """
        super().setup()  # Reads self.input_data from YAML

        if 'chisel_pass1' not in self.input_data:
            self.error("Missing 'chisel_pass1' in input YAML (did you run v2chisel_pass1 first?)")

        # Attempt to load prompt3.yaml for refinement if needed
        self.prompt3_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'prompt3.yaml')
        self.refine_llm = None

        if os.path.exists(self.prompt3_path):
            llm_args = self.input_data.get('llm', {})
            if llm_args:
                prompt3_template = LLM_template(self.prompt3_path)
                self.refine_llm = LLM_wrap()
                self.refine_llm.from_dict(name='v2chisel_fix_refine', conf_dict=llm_args, prompt=prompt3_template)
                print('[INFO] Loaded prompt3.yaml and initialized LLM for refinement.')
            else:
                print("[WARN] prompt3.yaml found but no 'llm' config. Can't refine automatically.")
        else:
            print('[WARN] prompt3.yaml not found, cannot refine if LEC fails.')

        # Provide a default iteration limit (could also read from input_data if desired)
        self.lec_limit = 10
        self.setup_called = True

    def run(self, data):
        """
        Main pass logic:
          1) Reads 'chisel_pass1' data (the code we want to fix or verify).
          2) Calls LEC (via equiv_check) to see if the code is logically equivalent.
          3) If LEC fails, refine code up to lec_limit times (LLM + chisel2v + eq check).
          4) Writes final 'chisel_fixed' field to the YAML.
        """
        pass1_info = data['chisel_pass1']
        chisel_changed = pass1_info.get('chisel_changed', '')
        verilog_candidate = pass1_info.get('verilog_candidate', '')
        was_valid = pass1_info.get('was_valid', False)
        self.verilog_fixed = data.get('verilog_fixed', '')

        print(f'[INFO] v2chisel_fix: Starting LEC check. was_valid={was_valid}')

        # Step 1: compare 'verilog_candidate' to 'verilog_fixed'
        verilog_fixed = data.get('verilog_fixed', '')
        if not verilog_fixed:
            print("[WARN] No 'verilog_fixed' in input. Skipping initial LEC check.")
            is_equiv = False
            lec_error = 'No verilog_fixed provided'
        else:
            is_equiv, lec_error = self._check_equivalence(verilog_fixed, verilog_candidate)

        refined_chisel = chisel_changed
        iteration_count = 0  # track how many times we refine

        # Step 2: If LEC fails, refine iteratively
        if not is_equiv:
            print(f'[WARN] LEC check failed/skipped. Attempting up to {self.lec_limit} refinements.')
            for attempt in range(1, self.lec_limit + 1):
                iteration_count = attempt
                print(f'\n[DEBUG] ------------- Refinement Attempt {attempt}/{self.lec_limit} ----------')
                print(f"[DEBUG] Current LEC error: {lec_error or 'None'}")

                # (A) Possibly refine code with LLM
                new_chisel = self._refine_chisel_code(refined_chisel, lec_error)
                if not new_chisel or new_chisel.strip() == refined_chisel.strip():
                    print('[INFO] LLM did not improve or returned empty code. Stopping refinement here.')
                    break

                refined_chisel = new_chisel
                print(f'[DEBUG] Updated refined_chisel:\n{refined_chisel}')

                # (B) Generate new Verilog from refined code
                new_verilog, gen_error = self._generate_verilog(refined_chisel, 'my_chisel2v_shared')
                if not new_verilog:
                    lec_error = gen_error or 'Chisel2v failed'
                    print(f'[ERROR] Verilog generation failed on iteration {attempt}: {lec_error}')
                    continue
                print(f'[DEBUG] Generated new Verilog:\n{new_verilog}')

                # (C) Check equivalence again
                is_equiv, lec_error = self._check_equivalence(verilog_fixed, new_verilog)
                if is_equiv:
                    print(f'[INFO] LEC check passed after refinement on iteration {attempt}!')
                    verilog_candidate = new_verilog
                    break
                else:
                    print(f'[DEBUG] LEC still failing after iteration {attempt}. lec_error={lec_error}')

            if not is_equiv:
                if iteration_count < self.lec_limit:
                    print(f'[WARN] Exiting early on iteration {iteration_count} due to error or no improvement.')
                else:
                    print(f'[WARN] Reached maximum attempts ({self.lec_limit}) without passing LEC.')
        else:
            print('[INFO] Code is already equivalent, no refinement needed.')

        # Step 3: Write final 'chisel_fixed' to output
        result = data.copy()
        result['chisel_fixed'] = {
            'original_chisel': data.get('chisel_original', ''),
            'refined_chisel': refined_chisel,
            'equiv_passed': is_equiv,
        }
        print("[INFO] v2chisel_fix: Done. 'chisel_fixed' written to output YAML.")
        return result

    # ---------------------------------------------------------------------
    # Helper: Check equivalence with verilog_fixed vs. verilog_candidate
    # ---------------------------------------------------------------------
    def _check_equivalence(self, gold_code: str, reference_code: str):
        """
        Returns (is_equiv: bool, lec_error: str or None).
        Logs debug info about Yosys result.
        """
        if not gold_code.strip() or not reference_code.strip():
            return (False, 'Missing code for equivalence check')

        eq_checker = Equiv_check()
        if not eq_checker.setup():
            err = eq_checker.get_error() or 'Yosys not found'
            print(f'[ERROR] Equiv_check setup failed: {err}')
            return (False, err)

        try:
            result = eq_checker.check_equivalence(gold_code, reference_code)
            if result is True:
                print('[INFO] LEC check: Designs are equivalent!')
                return (True, None)
            elif result is False:
                cex_info = eq_checker.get_counterexample()
                print('[WARN] LEC check: Designs are NOT equivalent.')
                if cex_info:
                    print(f'[DEBUG] LEC Counterexample info: {cex_info}')
                return (False, cex_info or 'LEC mismatch')
            else:
                err = eq_checker.get_error() or 'LEC result is None/inconclusive'
                print(f'[ERROR] LEC result is None. {err}')
                return (False, err)
        except Exception as e:
            print(f'[ERROR] LEC threw exception: {e}')
            return (False, str(e))

    # ---------------------------------------------------------------------
    # Helper: Use LLM to refine Chisel code (if available)
    # ---------------------------------------------------------------------
    def _refine_chisel_code(self, current_code: str, lec_error: str):
        """
        Provide the code + LEC error to the LLM (prompt3.yaml) in a single conversation.
        Returns the new refined code, or the same code if none/improvement is empty.
        """
        if not self.refine_llm:
            print('[WARN] No LLM available for refinement.')
            return current_code

        # This dictionary matches the placeholders in prompt3.yaml:
        #   {chisel_code}
        #   {lec_output}
        prompt_dict = {
            'chisel_code': current_code,
            'lec_output': lec_error or 'LEC failed',
            'verilog_fixed': self.verilog_fixed
        }

        # print(f'[DEBUG] prompt_dict to LLM (using prompt3.yaml): {prompt_dict}')

        # --- Print the EXACT text about to be sent to the LLM ---
        formatted = self.refine_llm.chat_template.format(prompt_dict)
        print("\n----- LLM FINAL MESSAGES TO SEND (prompt3.yaml) -----")
        for chunk in formatted:
            print(f"Role: {chunk['role']}")
            print("Content:")
            print(chunk['content'])
            print("--------------------------------------------------")
    

        # We use `chat(...)` so that we maintain a single conversation.
        response_text = self.refine_llm.chat(prompt_dict)
        print(f'[DEBUG] LLM raw chat response:\n{response_text}')

        # If there's no response or it's empty, do not update the code.
        if not response_text.strip():
            print('[ERROR] LLM returned empty chat response. Keeping old code.')
            return current_code

        # Strip markdown fences or triple backticks from the code
        new_code = self._strip_markdown_fences(response_text.strip())
        if not new_code:
            print('[ERROR] After removing backticks/fences, code is empty. Keeping old code.')
            return current_code

        print('[INFO] LLM provided a refined Chisel snippet (single conversation).')
        return new_code

    # ---------------------------------------------------------------------
    # Helper: Convert refined Chisel code => Verilog
    # ---------------------------------------------------------------------
    def _generate_verilog(self, chisel_code, shared_dir):
        """
        Runs Chisel2v on the given code. Returns (verilog_str, error_str).
        Includes debug printing for clarity.
        """
        if not chisel_code.strip():
            return (None, 'No Chisel code to generate Verilog from.')

        c2v = Chisel2v()
        c2v.working_dir = os.path.join(os.getcwd(), shared_dir)
        os.makedirs(c2v.working_dir, exist_ok=True)

        if not c2v.setup():
            return (None, c2v.error_message or 'Chisel2v setup failed')

        try:
            module_name = self._find_chisel_classname(chisel_code)
            verilog_output = c2v.generate_verilog(chisel_code, module_name)
            if 'module' not in verilog_output:
                return (None, "Generated Verilog missing 'module' keyword.")
            return (verilog_output, None)
        except Exception as e:
            return (None, f'Exception in Chisel2v: {e}')

    # ---------------------------------------------------------------------
    # Helper: parse 'class MyFoo extends Module'
    # ---------------------------------------------------------------------
    def _find_chisel_classname(self, chisel_code: str) -> str:
        match = re.search(r'class\s+([A-Za-z0-9_]+)\s+extends\s+Module', chisel_code)
        if match:
            return match.group(1)
        return 'MyModule'  # fallback name

    # ---------------------------------------------------------------------
    # Internal helper to remove triple backticks from the LLM response
    # ---------------------------------------------------------------------
    def _strip_markdown_fences(self, code_str: str) -> str:
        """Remove ```scala, ```verilog, or generic triple backticks from code_str."""
        code_str = re.sub(r'```[a-zA-Z]*\n?', '', code_str)
        code_str = re.sub(r'\n?```', '', code_str)
        return code_str.strip()


if __name__ == '__main__':  # pragma: no cover
    step = V2ChiselFix()
    step.parse_arguments()
    step.setup()
    step.step()
