#!/usr/bin/env python3
# See LICENSE for details

import os
import re
import difflib
import argparse
from ruamel.yaml import YAML
from ruamel.yaml.scalarstring import LiteralScalarString

from hagent.core.step import Step
from hagent.core.llm_template import LLM_template
from hagent.core.llm_wrap import LLM_wrap

from hagent.tool.chisel2v import Chisel2v
from hagent.tool.chisel_diff_applier import ChiselDiffApplier

from hagent.tool.extract_verilog_diff_keywords import FuzzyGrepFilter
from hagent.tool.filter_lines import FilterLines
from hagent.tool.fuzzy_grep import Fuzzy_grep
import tempfile
from hagent.tool.extract_code import Extract_code_verilog, Extract_code_chisel

def union_hints(hints1: str, hints2: str) -> str:
    import re
    union_dict = {}
    # This regex captures an optional arrow marker, the line number, and the content.
    pattern = re.compile(r'^\s*(?P<arrow>->)?\s*(?P<lineno>\d+):\s*(?P<content>.*)$')
    for hint in (hints1, hints2):
        for line in hint.splitlines():
            match = pattern.match(line)
            if match:
                lineno = int(match.group('lineno'))
                has_arrow = match.group('arrow') is not None
                content = match.group('content').rstrip()
                if lineno in union_dict:
                    prev_arrow, prev_content = union_dict[lineno]
                    # Combine arrow flags: if either occurrence had an arrow, we flag it.
                    combined_arrow = prev_arrow or has_arrow
                    # If the new occurrence has an arrow, favor its content.
                    chosen_content = content if has_arrow else prev_content
                    union_dict[lineno] = (combined_arrow, chosen_content)
                else:
                    union_dict[lineno] = (has_arrow, content)
    
    # Determine maximum width of the line numbers.
    width = max(len(str(ln)) for ln in union_dict)
    
    sorted_lines = []
    for lineno in sorted(union_dict.keys()):
        arrow, content = union_dict[lineno]
        # Build a fixed marker field of width 4:
        # If arrow exists, "->" is used; otherwise, four spaces.
        marker_field = f"{'->' if arrow else '':4}"
        # Format the line number right aligned in a field of width 'width'
        sorted_lines.append(f"{marker_field} {lineno:>{width}}: {content}")
    return "\n".join(sorted_lines)

class V2Chisel_pass1(Step):
    def setup(self):
        self.overwrite_conf = {}
        super().setup()
        print(f"input_file: {self.input_file}")

        self.verilog_extractor = Extract_code_verilog()
        self.chisel_extractor = Extract_code_chisel()

        if 'llm' not in self.input_data:
            self.error("Missing 'llm' section in input YAML")

        # Load the single prompt configuration file.
        conf_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'v2chisel_pass1_conf.yaml')
        if not os.path.exists(conf_file):
            self.error(f'Prompt file not found: {conf_file}')

        # Load the entire configuration from the YAML file.
        # We assume that LLM_template can load a file and expose the config via .config.
        self.template_config = LLM_template(conf_file)

        # llm_args = self.input_data['llm'] 
        llm_args = self.template_config.template_dict.get('v2chisel_pass1', {}).get('llm', {})

        self.lw = LLM_wrap(name='v2chisel_pass1', log_file="v2chisel_pass1.log", conf_file=conf_file, overwrite_conf=llm_args)
        if self.lw.last_error:
            raise ValueError(self.lw.last_error)
        self.setup_called = True

    def _generate_diff(self, old_code: str, new_code: str) -> str:
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
        # --- Fuzzy_grep part ---
            keywords = FuzzyGrepFilter.extract_keywords_from_diff(verilog_diff)
            print("------------------------------------------------")
            print("Extracted keywords from verilog diff:")
            print(keywords)
            print("------------------------------------------------")
            fg = Fuzzy_grep()
            if not fg.setup("chisel"):
                self.error("Fuzzy_grep setup failed: " + fg.error_message)
            
            default_threshold = self.input_data.get("threshold", 40)
            threshold_value = threshold_override if threshold_override is not None else default_threshold
            print("Using fuzzy grep threshold:", threshold_value)
            context_value = self.input_data.get("context", 1)
            print("Using fuzzy grep context:", context_value)
    
            search_results = fg.search(text=chisel_code, search_terms=keywords, context=context_value, threshold=threshold_value)
            fuzzy_hints = ""
            if "text" in search_results:
                matching_lines = []
                for (lineno, line, central) in search_results["text"]:
                    marker = "->" if central else "  "
                    matching_lines.append(f"{marker}{lineno:4d}: {line}")
                fuzzy_hints = "\n".join(matching_lines)
    
            print("------------------------------------------------")
            print("Extracted hint lines from fuzzy grep:")
            print(fuzzy_hints)
            print("------------------------------------------------")
    
            # --- FilterLines part ---
            fl = FilterLines()
            import tempfile, os
            with tempfile.NamedTemporaryFile(mode='w+', delete=False) as diff_temp:
                diff_temp.write(verilog_diff)
                diff_temp.flush()
                diff_file = diff_temp.name
            with tempfile.NamedTemporaryFile(mode='w+', delete=False) as chisel_temp:
                chisel_temp.write(chisel_code)
                chisel_temp.flush()
                chisel_file = chisel_temp.name
            try:
                filter_hints = fl.filter_lines(diff_file, chisel_file, context=1)
            finally:
                os.remove(diff_file)
                os.remove(chisel_file)
    
            print("------------------------------------------------")
            print("Extracted hint lines from filter_lines:")
            print(filter_hints)
            print("------------------------------------------------")
    
            final_hints = union_hints(fuzzy_hints, filter_hints)
            if not final_hints.strip():
                self.error("No hint lines extracted from either method. Aborting LLM call.")
            print("------------------------------------------------")
            print("Final union of hint lines:")
            print(final_hints)
            print("------------------------------------------------")
            return final_hints


    def _strip_markdown_fences(self, code_str: str) -> str:
        code_str = re.sub(r'```[a-zA-Z]*', '', code_str)
        code_str = code_str.replace('```', '').strip()
        return code_str

    def _fix_formatting(self, code: str) -> str:
        fixed = code.replace("\\n", "\n").replace("\\t", "\t")
        return fixed

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

    def run(self, data):
        verilog_original = data.get('verilog_original', '')
        verilog_fixed = data.get('verilog_fixed', '')
        chisel_original = data.get('chisel_original', '')

        verilog_diff_text = self._generate_diff(verilog_original, verilog_fixed)
        print("************************** Generated Verilog Diff **************************")
        print(verilog_diff_text)
        print("****************************************************")

        # default_threshold = self.input_data.get("threshold", 40)
        default_threshold = self.template_config.template_dict.get('v2chisel_pass1', {}).get('threshold', 40)
        chisel_subset = self._extract_chisel_subset(chisel_original, verilog_diff_text)
        if not chisel_subset.strip():
            self.error("No hint lines extracted from the Chisel code. Aborting LLM call.")

        max_iterations = 5
        was_valid = False
        chisel_updated_final = None
        verilog_candidate_final = None
        last_error_msg = ''
        generated_diff = ''

        # For a single prompt file, extract the desired section from the loaded config.
        # We assume self.template_config.config is a dictionary with keys like "prompt1", "prompt2", etc.
        full_config = self.template_config.template_dict.get(self.lw.name.lower(), {})
        if not full_config:
            full_config = self.template_config.template_dict
        

        for attempt in range(1, 5):
            if attempt == 1:
                if "prompt1" in full_config:
                    prompt_section = full_config["prompt1"]
                else:
                    self.error("Missing 'prompt1' section in prompt configuration.")
            elif attempt == 2:
                if "prompt2" in full_config:
                    prompt_section = full_config["prompt2"]
                else:
                    self.error("Missing 'prompt2' section in prompt configuration.")
            elif attempt == 3:
                if "prompt3" in full_config:
                    prompt_section = full_config["prompt3"]
                else:
                    self.error("Missing 'prompt3' section in prompt configuration.")
                increased_threshold = default_threshold + 20
                chisel_subset = self._extract_chisel_subset(chisel_original, verilog_diff_text, threshold_override=increased_threshold)
                if not chisel_subset.strip():
                    self.error("No hint lines extracted for attempt 3. Aborting LLM call.")
            else:
                if "prompt4" in full_config:
                    prompt_section = full_config["prompt4"]
                else:
                    self.error("Missing 'prompt4' section in prompt configuration.")
                decreased_threshold = default_threshold - 20
                chisel_subset = self._extract_chisel_subset(chisel_original, verilog_diff_text, threshold_override=decreased_threshold)
                if not chisel_subset.strip():
                    self.error("No hint lines extracted for attempt 3. Aborting LLM call.")

            # Create a new LLM_template instance from the selected section.
            prompt_template = LLM_template(prompt_section)
            if attempt == 1:
                self.lw.chat_template = prompt_template
            else:
                self.lw.name = f'v2chisel_pass1_retry_{attempt}'
                self.lw.chat_template = prompt_template

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

            # Debug: print the loaded prompt template
            print("DEBUG: Loaded prompt template for attempt {}:".format(attempt))
            print(prompt_template.config if hasattr(prompt_template, 'config') else prompt_template)

            formatted_prompt = self.lw.chat_template.format(prompt_dict)
            print('\n================ LLM QUERY (attempt {}) ================'.format(attempt))
            for chunk in formatted_prompt:
                print("Role: {}".format(chunk.get('role', '<no role>')))
                print("Content:")
                print(chunk.get('content', '<no content>'))
                print("------------------------------------------------")

            response_list = self.lw.inference(prompt_dict, prompt_index="prompt1", n=1)
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

def wrap_literals(obj):
    if isinstance(obj, dict):
        return {k: wrap_literals(v) for k, v in obj.items()}
    elif isinstance(obj, list):
        return [wrap_literals(elem) for elem in obj]
    elif isinstance(obj, str) and "\n" in obj:
        return LiteralScalarString(obj)
    else:
        return obj

def parse_arguments():
    parser = argparse.ArgumentParser()
    # The -o flag is required for the output file
    parser.add_argument('-o', required=True, help='Output YAML file')
    # Add a positional argument for the input file
    parser.add_argument('input_file', help='Input YAML file')
    return parser.parse_args()

if __name__ == '__main__':  # pragma: no cover
    args = parse_arguments()
    step = V2Chisel_pass1()
    step.parse_arguments()
    step.setup()
    result = step.step()  # this returns your result dictionary

    result = wrap_literals(result)
    
    yaml = YAML()
    yaml.default_flow_style = False  # use block style formatting
    yaml.indent(mapping=2, sequence=4, offset=2)
    
    with open(args.o, 'w') as out_file:
        yaml.dump(result, out_file)