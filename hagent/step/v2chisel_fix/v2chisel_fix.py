#!/usr/bin/env python3
# See LICENSE for details

"""
# V2ChiselFix

**V2ChiselFix** is a step in the hardware design automation pipeline designed to refine Chisel code based on Logic Equivalence Check (LEC) results. It leverages a Language Model (LLM) to iteratively improve Chisel code when discrepancies are found between generated Verilog and fixed Verilog specifications.

## Usage

Run the pass using Poetry:

```bash
poetry run python3 hagent/step/v2chisel_fix/v2chisel_fix.py -o hagent/step/v2chisel_fix/out2.yaml hagent/step/v2chisel_pass1/out2.yaml

Process Overview
Reads 'chisel_pass1' data.
Calls LEC to verify if verilog_candidate is equivalent to verilog_fixed.
If LEC fails:
Attempt 1: Uses prompt3 for refinement.
Attempt 2: If prompt3 does not improve the code, uses prompt4 (which employs additional hints generated via Fuzzy_grep).
If prompt4 also fails to yield a fix, the test case is marked as a failure.
Returns final data with "chisel_fixed" in the YAML.
"""

import os
import re
import difflib
from hagent.core.step import Step
from hagent.core.llm_wrap import LLM_wrap
from hagent.core.llm_template import LLM_template

from hagent.tool.extract_code import Extract_code_verilog, Extract_code_chisel
from hagent.tool.equiv_check import Equiv_check
from hagent.tool.compile_slang import Compile_slang
from hagent.tool.chisel2v import Chisel2v
from hagent.tool.chisel_diff_applier import ChiselDiffApplier
from hagent.step.v2chisel_pass1.v2chisel_pass1 import V2Chisel_pass1
from hagent.tool.react import React
from hagent.tool.compile import Diagnostic
from hagent.step.unified_diff.unified_diff import Unified_diff
from hagent.step.extract_hints.extract_hints import Extract_hints


import subprocess
import tempfile
import os

def diff_code(text1: str, text2: str) -> str:
    """
    Create a diff of two text arguments using:
      diff -bBdNrw -U5
    """
    # Create temporary files to hold the texts
    with tempfile.NamedTemporaryFile('w+', delete=False) as f1, \
         tempfile.NamedTemporaryFile('w+', delete=False) as f2:
        f1.write(text1)
        f1.flush()  # Ensure data is written to disk
        f2.write(text2)
        f2.flush()
        file1_name = f1.name
        file2_name = f2.name

    try:
        # Execute the diff command with the given options
        result = subprocess.run(
            ['diff', '-bBdNrw', '-U5', file1_name, file2_name],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True
        )
        return result.stdout
    finally:
        # Clean up temporary files to avoid resource leakage
        os.unlink(file1_name)
        os.unlink(file2_name)

class V2chisel_fix(Step):
    def setup(self):
        self.overwrite_conf = {}
        conf_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'v2chisel_base_conf.yaml')
        if not os.path.exists(conf_file):
            self.error(f'Prompt file not found: {conf_file}')

        super().setup()  # Reads self.input_data from YAML

        # FIXME: rename all chisel_pass1 to v2chisel_fix for yaml files
        if 'chisel_pass1' not in self.input_data:
            self.error("Missing 'chisel_pass1' in input YAML (did you run v2chisel_pass1 first?)")

        # Just load the strings here; defer diff until after initial LEC check
        self.verilog_fixed_str   = self.input_data.get('verilog_fixed', '')
        self.verilog_original_str = self.input_data.get('verilog_original', '')
        self.verilog_diff_str     = ""
        
        self.template_config = LLM_template(conf_file)
        self.base_metadata_context = self.input_data.get('metadata_context', 40)
        self.meta = self.base_metadata_context
        self.max_retries = 3
        # llm_args = self.input_data['llm'] 
        llm_args = self.template_config.template_dict.get('v2chisel_pass1', {}).get('llm', {})

        self.refine_llm = LLM_wrap(name='v2chisel_fix', conf_file=conf_file, log_file="v2chisel_fix.log", overwrite_conf=llm_args)

        self.verilog_extractor = Extract_code_verilog()
        self.chisel_extractor = Extract_code_chisel()

        self.setup_called = True

    def run(self, data):
        """
        1) Reads 'chisel_pass1' data.
        2) Checks if verilog_candidate is equivalent to verilog_fixed.
        3) If LEC fails, performs refinement in two phases:
           - Phase 1: Uses prompt3 (up to 2 attempts) to generate a Chisel diff.
           - Phase 2: If prompt3 fails, uses prompt4 (up to 2 attempts) similarly.
           In each attempt, the generated diff is applied to the original Chisel code,
           the updated code is compiled (Chisel2v) and then checked via LEC.
        4) Returns final data with "chisel_fixed" in the YAML.
        """
        # Only compute and print the unified diff if we have a fixed design to compare
        # if self.verilog_fixed_str.strip():
        #     self.verilog_diff_str = diff_code(self.verilog_original_str, self.verilog_fixed_str)
        #     print(f"[V2ChiselFix] Computed unified diff:\n{self.verilog_diff_str}")

        result = data.copy()
        pass1_info = data['chisel_pass1']
        chisel_changed = pass1_info.get('chisel_changed', '')
        verilog_candidate = pass1_info.get('verilog_candidate', '')
        was_valid = pass1_info.get('was_valid', False)
        # original_chisel = pass1_info.get('chisel_original', '')
        chisel_original = data.get('chisel_original', '')
        self.chisel_original = chisel_original
        self.chisel_subset = pass1_info.get('chisel_subset', chisel_changed)

        # print(f"[V2ChiselFix] Using extracted chisel_subset:\n{self.chisel_subset}")
        lec_flag = data.get('lec', 0)

        result['chisel_fixed'] = {
            'original_chisel': chisel_original,
            'refined_chisel': chisel_changed,  # to be updated upon successful refinement
            'chisel_diff': "",                 # the diff generated by the LLM
            'equiv_passed': False,
        }

        print(f'[INFO] Starting initial LEC check. was_valid={was_valid}')
        verilog_fixed = data.get('verilog_fixed', '')

        if lec_flag == 1:
            print("[INFO] 'lec' flag is set to 1. Skipping LEC check.")
            initial_equiv = True
            lec_error = None
        elif not verilog_fixed.strip():
            print("[WARN] No 'verilog_fixed' provided. Skipping initial LEC check.")
            initial_equiv = False
            lec_error = 'No verilog_fixed provided'
        else:
            initial_equiv, lec_error = self._check_equivalence(verilog_fixed, verilog_candidate)
            # If not equivalent, lec_error may be a list of (module, io) tuples
            if initial_equiv is False and isinstance(lec_error, list):
                print("[WARN] LEC found mismatches in the following signals:")
                for module_name, io_name in lec_error:
                    print(f"  • Module \"{module_name}\", IO \"{io_name}\"")

        if initial_equiv:
            print('[INFO] Designs are already equivalent; no refinement needed.')
            result['chisel_fixed']['refined_chisel'] = chisel_original
            result['chisel_fixed']['equiv_passed'] = True
            result['chisel_fixed']['chisel_diff'] = ""
            result['lec'] = 1
            return result

        # --- initial LEC failed: compute unified diff once for all prompts ---
        if self.verilog_fixed_str.strip():
            diff_step = Unified_diff()
            diff_step.set_io(self.input_file, self.output_file)
            diff_step.input_data = {
                'verilog_original': self.verilog_original_str,
                'verilog_fixed':    self.verilog_fixed_str,
            }
            diff_step.setup()
            tmp = diff_step.run({'verilog_original': self.verilog_original_str,
                                 'verilog_fixed':    self.verilog_fixed_str})
            self.verilog_diff_str = tmp['verilog_diff']
            print(f"[V2ChiselFix] Computed unified verilog_diff:\n{self.verilog_diff_str}")
            
        # --- Phase 1: prompt3 refinements (up to 2 attempts) ---
        prompt3_iteration = 1
        for attempt in range(1, prompt3_iteration + 1):
            print(f"[V2ChiselFix] prompt3 refinement attempt {attempt}")
            self.meta = self.base_metadata_context + 20 * (attempt)
            print(f"[V2ChiselFix] using metadata_context = {self.meta}")
            self.input_data['metadata_context'] = self.meta
            hint_step = Extract_hints(metadata_context=self.meta)
            hint_step.set_io(self.input_file, self.output_file)
            hint_step.input_data = {
                'verilog_original':  self.verilog_original_str,
                'verilog_fixed':     self.verilog_fixed_str,
                'verilog_diff':      self.verilog_diff_str,
                'chisel_original':   self.chisel_original,
                'metadata_context':  self.meta,
            }
            hint_step.setup()
            hint_out = hint_step.run(hint_step.input_data)
            self.chisel_subset = hint_out.get('hints', '').strip()
            print(
                f"[V2ChiselFix] regenerated chisel_subset "
                f"with metadata_context={self.meta}:\n{self.chisel_subset}"
            )

            # now call the LLM with fresh hints
            new_diff = self._refine_chisel_code(chisel_original, lec_error, attempt)

            if not new_diff.strip():
                continue
            # cand_code = ChiselDiffApplier().apply_diff(new_diff, chisel_original)
            cand_code = self._apply_diff(chisel_original, new_diff)
            ok, verilog_temp, err = self._run_chisel2v(cand_code)
            if not ok:
                cand_code = self._iterative_compile_fix(cand_code, err)
                ok, verilog_temp, err = self._run_chisel2v(cand_code)
                if not ok:
                    self.error("Compilation still failing after prompt_compiler_fix")
            equiv, lec_error = self._check_equivalence(self.verilog_fixed_str, verilog_temp)
            if equiv:
                print(f"[V2ChiselFix] prompt3 succeeded on attempt {attempt}")
                result['chisel_fixed'] = {
                    'original_chisel': chisel_original,
                    'refined_chisel':  cand_code,
                    'chisel_diff':     new_diff,
                    'metadata_context':  self.meta,
                    'equiv_passed':    True,
                }
                result['lec'] = 1
                return result

        # --- Phase 2: prompt4 refinements (up to 2 attempts) ---
        prompt4_iteration = 1
        last_prompt4_diff = ""
        for attempt in range(1, prompt4_iteration + 1):
            print(f"[V2ChiselFix] prompt4 refinement attempt {attempt}")
            self.meta = self.base_metadata_context + 30 * (attempt)
            self.input_data['metadata_context'] = self.meta
            hint_step = Extract_hints(metadata_context=self.meta)
            hint_step.set_io(self.input_file, self.output_file)
            hint_step.input_data = {
                'verilog_original':  self.verilog_original_str,
                'verilog_fixed':     self.verilog_fixed_str,
                'verilog_diff':      self.verilog_diff_str,
                'chisel_original':   self.chisel_original,
                'metadata_context':  self.meta,
            }
            hint_step.setup()
            hint_out = hint_step.run(hint_step.input_data)
            self.chisel_subset = hint_out.get('hints', '').strip()
            print(
                f"[V2ChiselFix] regenerated chisel_subset "
                f"with metadata_context={self.meta}:\n{self.chisel_subset}"
            )

            new_diff = self._refine_chisel_code_with_prompt4(chisel_original, lec_error, attempt)

            if not new_diff.strip():
                continue
            last_prompt4_diff = new_diff
            # cand_code = ChiselDiffApplier().apply_diff(new_diff, chisel_original)
            cand_code = self._apply_diff(chisel_original, new_diff)
            ok, verilog_temp, err = self._run_chisel2v(cand_code)
            if not ok:
                cand_code = self._iterative_compile_fix(cand_code, err)
                ok, verilog_temp, err = self._run_chisel2v(cand_code)
                if not ok:
                    self.error("Compilation still failing after prompt_compiler_fix")
            equiv, lec_error = self._check_equivalence(self.verilog_fixed_str, verilog_temp)
            if equiv:
                print(f"[V2ChiselFix] prompt4 succeeded on attempt {attempt}")
                result['chisel_fixed'] = {
                    'original_chisel': chisel_original,
                    'refined_chisel':  cand_code,
                    'chisel_diff':     new_diff,
                    'equiv_passed':    True,
                }
                result['lec'] = 1
                return result
            
        # --- Phase 3: prompt_lec_feedback refinement (if prompt4 failed) ---
        print("[V2ChiselFix] prompt_lec_feedback refinement")
        feedback_diff = self._refine_chisel_code_with_lec_feedback(
            chisel_original, last_prompt4_diff, lec_error
        )
        if feedback_diff.strip():
            cand_code = self._apply_diff(chisel_original, feedback_diff)
            ok, verilog_temp, err = self._run_chisel2v(cand_code)
            if ok:
                equiv, lec_error = self._check_equivalence(self.verilog_fixed_str, verilog_temp)
                if equiv:
                    print("[V2ChiselFix] prompt_lec_feedback succeeded")
                    result['chisel_fixed'] = {
                        'original_chisel': chisel_original,
                        'refined_chisel':  cand_code,
                        'chisel_diff':     feedback_diff,
                        'equiv_passed':    True,
                    }
                    result['lec'] = 1
                    return result

        # --- Fallback: React-driven refinement ---
        print("[V2ChiselFix] Both LLM phases failed, entering React-driven refinement")

        react_tool = React()
        if not react_tool.setup(db_path=None, learn=False, max_iterations=5, comment_prefix="//"):
            self.error("React setup failed: " + react_tool.error_message)

        initial_candidate = chisel_changed if chisel_changed.strip() else chisel_original
        # --- We will only get here if both LLM phases fail ---
        print(f"[V2ChiselFix] Calling React.react_cycle with initial_candidate length={len(initial_candidate)}")
        refined_chisel = react_tool.react_cycle(initial_candidate, self.check_callback, self.fix_callback)
        if not refined_chisel:
            print("[ERROR] React failed to refine the code.  Marking equivalence as failed.")
            result['chisel_fixed'] = {
                'original_chisel': chisel_original,
                'refined_chisel': chisel_original,
                'chisel_diff': new_diff,
                'equiv_passed': False,
            }
            result['lec'] = 0
            return result

        # React succeeded
        result['chisel_fixed'] = {
            'refined_chisel': refined_chisel,
            'equiv_passed': True,
            'chisel_diff': "diff not tracked in React integration",
        }
        result['lec'] = 1
        return result      
    
    def _extract_modules_from_lec_error(self, lec_error: str) -> list:
        """
        Parse the raw lec_error string for lines like:
          • Module "control", IO "_GEN_1"
        Return a de-duplicated list of module names, excluding any "<summary>" entries.
        """
        if not lec_error:
            return []

        # Find every occurrence of: Module "SomeName"
        pattern = r'Module\s+"([^"]+)"'
        matches = re.findall(pattern, lec_error)

        # Filter out placeholders (e.g. "<summary>") and de-duplicate while preserving order
        modules = [m for m in matches if not m.startswith('<')]
        unique_modules = list(dict.fromkeys(modules))
        return unique_modules
    
    def _extract_chisel_code_for_modules(self, chisel_text: str, module_names: list) -> str:
        """
        Given the full Chisel source (chisel_text) and a list of module names,
        locate each definition of `class <ModuleName> extends Module { … }` and extract
        that entire block (from the 'class' line through its matching closing '}').
        Return a single string concatenating all found blocks, separated by two newlines.
        """
        hints = []

        for mod in module_names:
            # Build a regex to find the 'class <mod> extends Module' line
            # We search for: class <mod> (optionally generic params) extends Module
            class_pattern = rf'class\s+{re.escape(mod)}\b.*?extends\s+Module'
            match = re.search(class_pattern, chisel_text)
            if not match:
                # If we didn’t find "class <mod> extends Module", skip it
                continue

            # The start index of the match
            start_idx = match.start()

            # Now locate the first '{' after the match—this begins the module body
            brace_open_idx = chisel_text.find('{', match.end())
            if brace_open_idx == -1:
                continue  # malformed or no body

            # Perform a simple brace‐counting to find the matching closing '}'
            depth = 0
            idx = brace_open_idx
            text_len = len(chisel_text)

            while idx < text_len:
                char = chisel_text[idx]
                if char == '{':
                    depth += 1
                elif char == '}':
                    depth -= 1
                    if depth == 0:
                        # Found the matching closing brace for this class
                        end_idx = idx
                        break
                idx += 1
            else:
                # If we exhausted the string without depth returning to 0, skip
                continue

            # Slice out from `start_idx` through `end_idx` (inclusive) to capture the whole class
            module_block = chisel_text[start_idx : end_idx + 1]
            hints.append(module_block.strip())

        # Join all found blocks with two newlines (for readability)
        return "\n\n".join(hints).strip()


    def _refine_chisel_code_with_lec_feedback(self, original: str, prev_diff: str, lec_error: str):
        """
        Uses prompt_lec_feedback to generate a new Chisel diff.
        The prompt includes the Verilog diff, the previous Chisel diff, the LEC error, and code hints.
        """
        
        # 1) Extract a de-duped list of module names from lec_error
        modules = self._extract_modules_from_lec_error(lec_error)

        # 2) From the full chisel_original, extract each module's code block
        chisel_original = original  # your original Chisel string from YAML
        module_hints_code = self._extract_chisel_code_for_modules(chisel_original, modules)

        # 3) Combine with any preexisting chisel_subset hints (if you still want them)
        combined_hints = module_hints_code
        if self.chisel_subset.strip():
            # If you do want to keep pass1 hints, you can prepend them:
            combined_hints = self.chisel_subset.strip() + "\n\n" + module_hints_code

        print(f"[V2ChiselFix] Modules from LEC error: {modules}")
        print(f"[V2ChiselFix] Extracted Chisel code hints for those modules:\n{module_hints_code}\n")

        # 4) Build and send the LLM prompt
        full_config = self.template_config.template_dict.get(self.refine_llm.name.lower(), {})
        prompt_template = LLM_template(full_config["prompt_lec_feedback"])
        self.refine_llm.chat_template = prompt_template

        prompt_dict = {
            'verilog_diff':            self.verilog_diff_str,
            'previous_chisel_diff':    prev_diff or "",
            'lec_error':               lec_error or "LEC failed",
            'chisel_hints':            combined_hints,
        }
        print('\n================ LLM QUERY (prompt_lec_feedback) ================')
        answers = self.refine_llm.inference(prompt_dict, prompt_index="prompt_lec_feedback", n=1, max_history=10)
        if not answers:
            print('\n=== LLM RESPONSE (prompt_lec_feedback): EMPTY ===\n')
            return ""

        print('\n================ LLM RESPONSE (prompt_lec_feedback) ================')
        print(answers[0])
        print('=====================================================================')

        for txt in answers:
            diff = self.chisel_extractor.parse(txt)
            if diff:
                return diff
        return ""

    def check_callback(self, code: str):
        # Use _run_chisel2v to compile and then _check_equivalence to verify the candidate.
        is_valid, verilog_candidate_temp, error_msg = self._run_chisel2v(code)
        if not is_valid:
            # Create a dummy diagnostic with the error message.
            return [Diagnostic(f"Compilation error: {error_msg}")]
        is_equiv, lec_err = self._check_equivalence(self.verilog_fixed_str, verilog_candidate_temp)
        if is_equiv:
            return []  # No diagnostics if equivalent.
        else:
            return [Diagnostic(f"LEC failed: {lec_err}")]
    def fix_callback(self, code: str, diag, fix_example, delta, iteration):
        # Use your prompt-based diff generation (prompt3) to attempt a fix.
        new_diff = self._refine_chisel_code(code, diag.msg, iteration)
        # applier = ChiselDiffApplier()
        # new_code = applier.apply_diff(new_diff, code)
        new_code = self._apply_diff(code, new_diff)
        return new_code

    def _check_candidate_with_compiler(self,candidate_verilog: str) -> (bool, str):
        """
        Uses Compile_slang to compile the candidate Verilog code.
        Returns a tuple (is_valid, error_message).
        """
        compiler = Compile_slang()
        if not compiler.setup():
            return (False, f"Compile_slang setup failed: {compiler.error_message}")
        if not compiler.add_inline(candidate_verilog):
            return (False, f"Failed to add candidate Verilog: {compiler.error_message}")
        errors = compiler.get_errors()
        if errors:
            error_messages = "\n".join([e.msg for e in errors])
            return (False, error_messages)
        return (True, "")

    def _iterative_compile_fix(self, chisel_code: str, compiler_error: str) -> str:
        max_iterations = 5
        current_code = chisel_code
        for i in range(1, max_iterations + 1):
            current_chisel_diff = diff_code(self.chisel_original, current_code)
            print("\ncurrent_chisel_diff:", current_chisel_diff)
            print("\n compiler_error:", compiler_error)

            prompt_dict = {
                'current_chisel_diff': current_chisel_diff,
                'compiler_error': compiler_error,
                'new_hints': self.chisel_subset,
            }

            full_config = self.template_config.template_dict.get(self.refine_llm.name.lower(), {})
            if "prompt_compiler_fix" not in full_config:
                self.error("Missing 'prompt_compiler_fix' in prompt configuration.")

            prompt_template = LLM_template(full_config["prompt_compiler_fix"])
            self.refine_llm.chat_template = prompt_template
            # formatted_prompt = self.refine_llm.chat_template.format(prompt_dict)
            print(f'\n================ LLM QUERY (prompt_compiler_fix, iteration {i}) ================')
            # for chunk in formatted_prompt:
            #     print("Role: {}".format(chunk.get('role', '<no role>')))
            #     print("Content:")
            #     print(chunk.get('content', '<no content>'))
            #     print("------------------------------------------------")
            answers = self.refine_llm.inference(prompt_dict, prompt_index="prompt_compiler_fix", n=1, max_history=10)
            if not answers:
                print('\n=== LLM RESPONSE: EMPTY ===\n')
                continue
            print('\n================ LLM RESPONSE (prompt_compiler_fix) ================')
            print(answers[0])
            print('======================================================================')
            for txt in answers:
                diff_code_text = self.chisel_extractor.parse(txt)
                if diff_code_text:
                    # applier = ChiselDiffApplier()
                    # new_code = applier.apply_diff(diff_code_text, current_code)
                    new_code = self._apply_diff(current_code, diff_code_text)
                    is_valid, verilog_candidate, error_msg = self._run_chisel2v(new_code)
                    if is_valid:
                        return new_code
                    else:
                        print(f'[WARN] Compiler still failing in iteration {i}: {error_msg}')
                        current_code = new_code
                        compiler_error = error_msg
                        break
        return current_code

    def _apply_diff(self, original: str, initial_diff: str) -> str:
        diff = initial_diff
        for attempt in range(1, self.max_retries + 1):
            try:
                chisel = ChiselDiffApplier().apply_diff(diff, original)
                print(f"[V2ChiselFix] Applied diff on attempt {attempt}")
                return chisel
            except RuntimeError as e:
                applier_error = str(e)
                print(f"[V2ChiselFix] Context error on attempt {attempt}: {applier_error}")
                # bump metadata_context by 20 lines per retry
                self.meta = self.base_metadata_context + 20 * attempt
                self.input_data['metadata_context'] = self.meta
                print(f"[V2ChiselFix] metadata_context increased to {self.meta}")

                # regenerate a better diff, now passing applier_error
                diff = self._refine_diff_not_found(diff, applier_error)
                print(f"[V2ChiselFix] obtained new diff, retrying (attempt {attempt})")

        # all retries exhausted
        raise RuntimeError(f"_apply_diff failed after {self.max_retries} attempts")
    

    def _refine_diff_not_found(self, old_diff: str, applier_error: str) -> str:
        """
        When Apply_diff fails due to missing context, regenerate hints
        at the current metadata_context and then ask the LLM for a better diff.
        """
        # 1) regenerate hint lines for this new metadata_context using Extract_hints directly
        print("metadate:", self.meta)

        hint_step = Extract_hints(metadata_context=self.meta)
        hint_step.set_io(self.input_file, self.output_file)
        hint_step.input_data = {
            'verilog_original': self.verilog_original_str,
            'verilog_fixed':    self.verilog_diff_str,  # pass the diff as before
            'verilog_diff':     self.verilog_diff_str,
            'chisel_original':  self.chisel_original,
            'metadata_context': self.meta,
        }
        hint_step.setup()
        hint_out = hint_step.run(hint_step.input_data)

        new_hints = hint_out.get('hints', '').strip()
        self.chisel_subset = new_hints
        print(f"[V2ChiselFix] regenerated chisel_subset for diff_not_found (meta={self.meta}):\n{self.chisel_subset}")


        # 2) now ask the LLM for a new diff with fresh hints
        cfg = self.template_config.template_dict[self.refine_llm.name.lower()]
        if 'prompt_diff_not_found' not in cfg:
            self.error("Missing 'prompt_diff_not_found' in prompt configuration.")
        self.refine_llm.chat_template = LLM_template(cfg['prompt_diff_not_found'])

        prompt = {
            'generate_diff':    old_diff,
            'metadata_context': self.meta,
            'new_hints':        self.chisel_subset,
            'applier_error':    applier_error,
            'verilog_diff':     self.verilog_diff_str,
        }

        answers = self.refine_llm.inference(prompt, 'prompt_diff_not_found', n=5)
        if not answers:
            print('\n=== LLM RESPONSE: EMPTY ===\n')

        print('\n================ LLM RESPONSE (prompt_not_found) ================')
        print(answers[0])
        print('======================================================================')

        for txt in answers:
            diff_candidate = self.chisel_extractor.parse(txt)
            if diff_candidate:
                return diff_candidate

        # 3) fallback to the original diff if LLM gives nothing usable
        return old_diff


    def _generate_diff(self, old_code: str, new_code: str) -> str:
        """
        Generate a unified diff string comparing old_code vs. new_code.
        """
        old_lines = old_code.splitlines()
        new_lines = new_code.splitlines()
        diff_lines = difflib.unified_diff(
            old_lines,
            new_lines,
            fromfile='Original version',
            tofile='Modified version',
            lineterm=''
        )
        return '\n'.join(diff_lines)

    def _check_equivalence(self, gold_code: str, gate_code: str):
        if not gold_code.strip() or not gate_code.strip():
            return (False, 'Missing code for equivalence check')
        eq_checker = Equiv_check()
        if not eq_checker.setup():
            err = eq_checker.get_error() or 'Yosys not found'
            print(f'[ERROR] Equiv_check setup failed: {err}')
            return (False, err)
        try:
            result = eq_checker.check_equivalence(gold_code, gate_code)
            if result is True:
                print('[INFO] LEC check: Designs are equivalent!')
                return (True, None)
            elif result is False:
                err = eq_checker.get_error()
                cex_info = eq_checker.get_counterexample()
                print('[WARN] LEC check: Designs are NOT equivalent.')
                
                if err:
                    print(f'[ERROR] LEC error: {err}')
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

    def _refine_chisel_code(self, current_code: str, lec_error: str, attempt: int):
        """
        Uses prompt3 for LLM refinement to generate a Chisel diff.
        The LLM (via prompt3.yaml) is instructed to output only the diff in unified diff format.
        """
        prompt_dict = {
            'chisel_original': self.chisel_original,
            'chisel_subset': self.chisel_subset,
            'lec_output': lec_error or 'LEC failed',
            'verilog_diff': self.verilog_diff_str,
            'metadata_context': self.meta,
        }
        if not self.chisel_subset.strip():
            self.error("No hint lines extracted from the Chisel code. Aborting LLM call.")

        full_config = self.template_config.template_dict.get(self.refine_llm.name.lower(), {})
        prompt_template = LLM_template(full_config["prompt3"])
        self.refine_llm.chat_template = prompt_template
        print('\n================ LLM QUERY (prompt3, attempt {}) ================'.format(attempt))
        answers = self.refine_llm.inference(prompt_dict, prompt_index="prompt3", n=1, max_history=10)
        if not answers:
            print('\n=== LLM RESPONSE: EMPTY ===\n')
            last_error_msg = 'LLM gave empty response'

        print('\n================ LLM RESPONSE (prompt3) ================')
        print(answers[0])
        print('==========================================================')

        for txt in answers:
            code = self.chisel_extractor.parse(txt)
            if code:
                return code

        return ""

    def _refine_chisel_code_with_prompt4(self, current_code: str, lec_error: str, attempt: int):
        """
        Uses prompt4 for LLM refinement to generate a Chisel diff.
        The LLM (via prompt4.yaml) is instructed to output only the diff in unified diff format.
        On extended attempts (attempt > 2), adjusts LLM parameters and uses an alternative prompt.
        """
        # Re-use pass1’s hint extractor: give it the same I/O and llm config
        v2c_pass1 = V2Chisel_pass1()
        # set I/O so setup() can read YAML / logs
        v2c_pass1.input_file   = self.input_file
        v2c_pass1.output_file  = self.output_file
        # include the llm override from pass1 config
        pass1_llm = self.template_config.template_dict.get('v2chisel_pass1', {}).get('llm', {})
        cfg = self.input_data.copy()
        cfg['llm'] = pass1_llm
        v2c_pass1.input_data   = cfg
        v2c_pass1.setup()
        # now extract fresh hints
        new_hints = v2c_pass1._extract_chisel_subset(
            self.chisel_original,
            self.verilog_diff_str,
            threshold_override=70
        )
        if not new_hints.strip():
            self.error("No hint lines extracted from the Chisel code. Aborting LLM call.")

        prompt_dict = {
            'lec_output': lec_error or 'LEC failed',
            'chisel_subset': self.chisel_subset,
            'verilog_diff': self.verilog_diff_str,
            'chisel_diff': self._generate_diff(self.chisel_original, current_code),
            'new_hints': new_hints,
            'n': 5,
        }

        full_config = self.template_config.template_dict.get(self.refine_llm.name.lower(), {})
        # Default to prompt4
        prompt_template = LLM_template(full_config["prompt4"])

        print('\n================ LLM QUERY (prompt4, attempt {}) ================'.format(attempt))
        # for key, value in prompt_dict.items():
        #     print(f"{key}: {value}")
        print('==============================================')

        # For extended attempts (attempt > 2), adjust LLM parameters and use an alternative prompt
        if attempt > 2:
            print("\n[INFO] Extended Prompt4 attempt: adjusting LLM parameters and using alternative prompt.")
            self.refine_llm.llm_args['top_k'] = 50
            self.refine_llm.llm_args['temperature'] = 0.9
            alt_prompt = full_config.get('prompt4_alternative', None)
            if not alt_prompt:
                self.error("Missing 'prompt4_alternative' section in configuration.")
            prompt_template = LLM_template(alt_prompt)
            answers = self.refine_llm.inference(prompt_dict, 'prompt4_alternative', n=3, max_history=10)
        else:
            answers = self.refine_llm.inference(prompt_dict, 'prompt4', n=1, max_history=10)

        self.refine_llm.chat_template = prompt_template
        formatted_prompt = self.refine_llm.chat_template.format(prompt_dict)
        print('\n================ LLM FORMATTED QUERY (prompt4, attempt {}) ================'.format(attempt))
        # for chunk in formatted_prompt:
        #     print("Role: {}".format(chunk.get('role', '<no role>')))
        #     print("Content:")
        #     print(chunk.get('content', '<no content>'))
        #     print("------------------------------------------------")

        if not answers:
            print('\n=== LLM RESPONSE: EMPTY ===\n')
            return ""

        print('\n================ LLM RESPONSE (prompt4) ================')
        if isinstance(answers, list) and len(answers) > 0:
            print(answers[0])
        print('==============================================')

        # If multiple candidates were requested (attempt > 2), evaluate each candidate:
        if attempt > 2 and isinstance(answers, list) and len(answers) > 1:
            for txt in answers:
                candidate_diff = self.chisel_extractor.parse(txt)
                if not candidate_diff:
                    continue
                print("[INFO] Evaluating candidate diff:")
                print(candidate_diff)
                # applier = ChiselDiffApplier()
                # test_code = applier.apply_diff(candidate_diff, self.chisel_original)
                test_code = self._apply_diff(self.chisel_original, candidate_diff)
                is_valid, verilog_candidate_temp, error_msg = self._run_chisel2v(test_code)
                if not is_valid:
                    print(f"[INFO] Candidate diff failed compilation: {error_msg}")
                    continue
                is_equiv, lec_error_candidate = self._check_equivalence(self.verilog_fixed_str, verilog_candidate_temp)
                if is_equiv:
                    print("[INFO] Candidate diff passed compilation and LEC check.")
                    return candidate_diff
                else:
                    print(f"[INFO] Candidate diff failed LEC: {lec_error_candidate}")
            return ""
        else:
            for txt in answers:
                candidate_diff = self.chisel_extractor.parse(txt)
                if candidate_diff:
                    return candidate_diff
            return ""

    def _run_chisel2v(self, chisel_code: str):
        """
        Runs the Chisel2v tool to generate Verilog from the given Chisel code and checks its validity.
        """
        if not chisel_code.strip():
            return (False, None, 'Chisel snippet is empty')
        c2v = Chisel2v()
        if not c2v.setup():
            return (False, None, 'chisel2v setup failed: ' + c2v.error_message)
        # module_name = self._find_chisel_classname(chisel_code)
        module_name = "Top"
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
        match = re.search(r'class\s+([A-Za-z0-9_]+)\s+extends\s+Module', chisel_code)
        if match:
            return match.group(1)
        return 'MyModule'

    def _strip_markdown_fences(self, code_str: str) -> str:
        code_str = re.sub(r'```[a-zA-Z]*\n?', '', code_str)
        code_str = re.sub(r'\n?```', '', code_str)
        return code_str.strip()


if __name__ == '__main__':  # pragma: no cover
    step = V2chisel_fix()
    step.parse_arguments()
    step.setup()
    step.step()
