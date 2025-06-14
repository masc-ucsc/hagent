#!/usr/bin/env python3
# See LICENSE for details

import os
import sys
import re
import difflib
import argparse
from ruamel.yaml import YAML
from ruamel.yaml.scalarstring import LiteralScalarString

from hagent.core.step import Step
from hagent.core.llm_template import LLM_template
from hagent.core.llm_wrap import LLM_wrap

from hagent.tool.chisel2v import Chisel2v
from hagent.tool.code_scope import Code_scope
# from hagent.step.apply_diff.apply_diff import Apply_diff
from hagent.tool.chisel_diff_applier import ChiselDiffApplier

from hagent.tool.extract_verilog_diff_keywords import Extract_verilog_diff_keywords
from hagent.tool.fuzzy_grep import Fuzzy_grep
from hagent.tool.extract_code import Extract_code_verilog, Extract_code_chisel
from hagent.tool.metadata_mapper import MetadataMapper
from hagent.step.extract_hints.extract_hints import Extract_hints
from hagent.step.generate_diff.generate_diff import Generate_diff
from hagent.step.verify_candidate.verify_candidate import Verify_candidate
from hagent.step.unified_diff.unified_diff import Unified_diff


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
        marker_field = f'{"->" if arrow else "":4}'
        # Format the line number right aligned in a field of width 'width'
        sorted_lines.append(f'{marker_field} {lineno:>{width}}: {content}')
    return '\n'.join(sorted_lines)


class V2Chisel_pass1(Step):
    def setup(self):
        self.overwrite_conf = {}
        super().setup()
        print(f'input_file: {self.input_file}')

        self.verilog_extractor = Extract_code_verilog()
        self.chisel_extractor = Extract_code_chisel()

        self.metadata_mapper = MetadataMapper(
            self.input_data.get('verilog_original', ''),
            self.input_data.get('verilog_fixed', '')
        )

        # Load the single prompt configuration file.
        conf_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'v2chisel_pass1_conf.yaml')
        if not os.path.exists(conf_file):
            self.error(f'Prompt file not found: {conf_file}')

        # Load the entire configuration from the YAML file.
        # We assume that LLM_template can load a file and expose the config via .config.
        self.template_config = LLM_template(conf_file)  # FIXME: Use a yaml loader, not a llm_template

        self.lw = LLM_wrap(
            name='v2chisel_pass1', log_file='v2chisel_pass1.log', conf_file=conf_file, overwrite_conf=self.input_data
        )
        if self.lw.last_error:
            raise ValueError(self.lw.last_error)
        self.setup_called = True

    # def _generate_diff(self, old_code: str, new_code: str) -> str:
    #     old_lines = old_code.splitlines()
    #     new_lines = new_code.splitlines()
    #     diff_lines = difflib.unified_diff(
    #         old_lines, new_lines, fromfile='verilog_original.v', tofile='verilog_fixed.v', lineterm='', n=20
    #     )
    #     return '\n'.join(diff_lines)

    def _is_snippet_empty(self, snippet: str) -> bool:
        """
        Returns True if no meaningful code line is marked in the snippet.
        """
        for line in snippet.splitlines():
            if line.startswith('->') and line.split(':', 1)[1].strip():
                return False
        return True

    def _extract_chisel_subset(self, chisel_code: str, verilog_diff: str, threshold_override: int = None) -> str:
        """
        Extract hints from the Chisel code. Use metadata-driven slices if available and not forced to fuzzy-grep.
        Otherwise (no metadata or force_fuzzy==True), fall back to fuzzy_grep.
        """
        # Check if fuzzy is forced via CLI (-fz)
        force_fuzzy = getattr(self, 'force_fuzzy', False)
        print("force_fuzzy:", force_fuzzy)

        # --- Metadata-driven hints ---
        metadata_pointers = self.metadata_mapper.pointers_for_diff(verilog_diff)
        
        # Only use metadata if pointers exist and fuzzy is NOT forced
        if metadata_pointers and not force_fuzzy:
            print('------------------------------------------------')
            print('Metadata pointers found:', metadata_pointers)
            print('------------------------------------------------')
            metadata_context = self.input_data.get('metadata_context', 10)
            print('Using metadata context =', metadata_context)
            snippet = self.metadata_mapper.slice_chisel_by_pointers(
                chisel_code, metadata_pointers, before=5, after=metadata_context
            )

            if not self._is_snippet_empty(snippet):
                print('------------------------------------------------')
                print('Chisel metadata-driven hints:')
                # print(snippet)
                # print('------------------------------------------------')
                return snippet

            print('Metadata-driven snippet empty, falling back to fuzzy-grep')
        else:
            if force_fuzzy:
                print('------------------------------------------------')
                print('Force fuzzy-grep enabled: skipping metadata-driven hints')
                print('------------------------------------------------')
            else:
                print('------------------------------------------------')
                print('No metadata pointers: using fuzzy-grep')
                print('------------------------------------------------')

        # --- Fuzzy_grep fallback ---
        keywords = Extract_verilog_diff_keywords.get_user_variables(verilog_diff)
        print('------------------------------------------------')
        print('Extracted keywords from verilog diff:', keywords)
        print('------------------------------------------------')

        fg = Fuzzy_grep()
        if not fg.setup('chisel'):
            self.error('Fuzzy_grep setup failed: ' + fg.error_message)

        default_threshold = self.input_data.get('threshold', 80)
        threshold_value = threshold_override if threshold_override is not None else default_threshold
        print('Using fuzzy grep threshold:', threshold_value)

        search_results = fg.search(text=chisel_code, search_terms=keywords, threshold=threshold_value)

        chisel_hints = ''
        if 'text' in search_results:
            hint_list = [pair[0] for pair in search_results['text']]
            cs = Code_scope(chisel_code)
            scopes = cs.find_nearest_upper_scopes(hint_list)
            for scope_pair in scopes:
                chisel_hints += f"Code snippet from {scope_pair[0]} to {scope_pair[1]}:\n"
                chisel_hints += cs.get_code(scope_pair, hint_list, '->')
                chisel_hints += "\n\n"

        print('------------------------------------------------')
        print('Chisel hints from Code_scope:')
        print(chisel_hints)

        return chisel_hints

    def _strip_markdown_fences(self, code_str: str) -> str:
        code_str = re.sub(r'```[a-zA-Z]*', '', code_str)
        code_str = code_str.replace('```', '').strip()
        return code_str

    def _fix_formatting(self, code: str) -> str:
        fixed = code.replace('\\n', '\n').replace('\\t', '\t')
        return fixed

    def run(self, data):
        verilog_original = data.get('verilog_original', '')
        verilog_fixed = data.get('verilog_fixed', '')
        chisel_original = data.get('chisel_original', '')

        # verilog_diff_text = self._generate_diff(verilog_original, verilog_fixed)
        # --- GENERATE UNIFIED DIFF VIA our new step ---
        # use the new UnifiedDiff step instead of the old helper
        diff_step = Unified_diff()
        diff_step.set_io(self.input_file, self.output_file)
        diff_step.input_data = {
            'verilog_original': verilog_original,
            'verilog_fixed':    verilog_fixed,
        }
        diff_step.setup()
        data = diff_step.run(data)
        verilog_diff_text = data['verilog_diff']
        print('*** Generated Verilog Diff ***')
        # print(verilog_diff_text)
        # print('********************************************************')

        # --- EXTRACT HINTS STEP ---
        default_threshold = self.template_config.template_dict.get('v2chisel_pass1', {}).get('threshold', 80)
        # seed the step’s inputs
        data['verilog_diff']    = verilog_diff_text
        data['chisel_original'] = chisel_original

        chisel_subset = self._extract_chisel_subset(
                chisel_original, verilog_diff_text
            )

        if not chisel_subset.strip():
            self.error('No hint lines extracted from the Chisel code. Aborting LLM call.')

        # seed hints for Generate_diff
        data['hints'] = chisel_subset

        # === GENERATE DIFF STEP ===
        print('>>> STEP 2: LLM-based Generate_diff')


        was_valid = False
        chisel_updated_final = None
        verilog_candidate_final = None
        last_error_msg = ''
        generated_diff = ''
        prompt_success      = dict.fromkeys(
        ['prompt0','prompt1','prompt2','prompt3','prompt4'], 0
        )

        # For a single prompt file, extract the desired section from the loaded config.
        # We assume self.template_config.config is a dictionary with keys like "prompt1", "prompt2", etc.
        full_config = self.template_config.template_dict\
        .get(self.lw.name.lower(), {}) or self.template_config.template_dict

        if not full_config:
            full_config = self.template_config.template_dict

        for attempt in range(1, 6):
            print(f"\n=== V2Chisel_pass1: Starting attempt {attempt} ===")
            prompt_index = f'prompt{attempt}'
            if prompt_index not in full_config:
                continue
            if attempt == 1:
                prompt_index = 'prompt0'
                prompt_section = full_config[prompt_index]
                print("\n prompt0")

            elif attempt == 2:
                prompt_index = 'prompt1'
                prompt_section = full_config[prompt_index]
                print("\n prompt1")
            elif attempt == 3:
                prompt_index = 'prompt2'
                prompt_section = full_config[prompt_index]
                print("\n prompt2")

            elif attempt == 4:
                prompt_index = 'prompt3'
                prompt_section = full_config[prompt_index]
                print("\n prompt3")

                increased_threshold = default_threshold + 10
                chisel_subset = self._extract_chisel_subset(
                    chisel_original, verilog_diff_text, threshold_override=increased_threshold
                )
                if not chisel_subset.strip():
                    self.error('No hint lines extracted for attempt 4. Aborting LLM call.')
            else:
                if 'prompt4' in full_config:
                    prompt_section = full_config['prompt4']
                    prompt_index = 'prompt4'
                    print("\n prompt4")

                decreased_threshold = default_threshold - 10
                chisel_subset = self._extract_chisel_subset(
                    chisel_original, verilog_diff_text, threshold_override=decreased_threshold
                )
                if not chisel_subset.strip():
                    self.error('No hint lines extracted for attempt 5. Aborting LLM call.')

            # Create a new LLM_template instance from the selected section.
            prompt_template = LLM_template(prompt_section)
            if attempt == 1:
                self.lw.chat_template = prompt_template
            else:
                self.lw.name = f'v2chisel_pass1_retry_{attempt}'
                self.lw.chat_template = prompt_template
            print(prompt_index)
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
            print('DEBUG: Loaded prompt template for attempt {}:'.format(attempt))
            print(prompt_template.config if hasattr(prompt_template, 'config') else prompt_template)

            response_list = self.lw.inference(prompt_dict, prompt_index=prompt_index, n=1)
            if not response_list:
                print('\n=== LLM RESPONSE: EMPTY ===\n')
                last_error_msg = 'LLM gave empty response'
                continue

            print('\n================ LLM RESPONSE ================')
            print(response_list[0])
            print('==============================================')

            generated_diff = self._strip_markdown_fences(response_list[0])
            # apply with ChiselDiffApplier instead of Apply_diff
            applier = ChiselDiffApplier()
            chisel_original = data.get('chisel_original', '')
            try:
                chisel_updated = applier.apply_diff(generated_diff, chisel_original)
                data['chisel_candidate'] = chisel_updated
            except Exception as ex:
                print("Applier has some errors.")
                err = str(ex)
                # also treat “removal lines not found” as a verification failure
                if 'apply_diff verification failed' in err \
                   or 'these removal lines not found' in err:
                    cu, new_diff, apply_ok = self._handle_diff_not_found(
                        data, generated_diff, err, verilog_diff_text, chisel_original
                    )
                    if apply_ok:
                        chisel_updated = cu
                        generated_diff = new_diff
                        print('Applied the diff after diff_not_found retry.')
                    else:
                        last_error_msg = err
                        continue
                else:
                    # any other exception we don’t know how to recover from
                    raise


            # delegate compilation & basic validity check to our new Verify_candidate step
            print("DEBUG: about to run Verify_candidate")
            verify = Verify_candidate()
            verify.set_io(self.input_file, self.output_file)
            verify.input_data = {'chisel_candidate': chisel_updated}
            verify.setup()
            verify_result = verify.run({'chisel_candidate': chisel_updated})
            is_valid       = verify_result.get('was_valid', False)
            print(f"DEBUG: Verify_candidate returned was_valid={is_valid}, error_msg={verify_result.get('error_msg')}")
            verilog_candidate = verify_result.get('verilog_candidate', None)
            error_msg      = verify_result.get('error_msg', '')
            if is_valid:
                prompt_success[prompt_index] = 1
                chisel_updated_final = chisel_updated
                verilog_candidate_final = self._fix_formatting(verilog_candidate)
                was_valid = True
                break
            else:
                print(f"DEBUG: Attempt {attempt} failed with error_msg: {error_msg}")
                last_error_msg = error_msg or 'Unknown chisel2v error'

        #End of the loop
        if not was_valid and chisel_updated_final is None:
            chisel_updated_final = 'No valid snippet generated.'

        result = data.copy()
        result['chisel_pass1'] = {
            'chisel_updated': chisel_updated_final,
            'generated_diff': generated_diff,
            'verilog_candidate': verilog_candidate_final,
            'was_valid': was_valid,
            'chisel_subset': chisel_subset,
            'prompt0': prompt_success['prompt0'],
            'prompt1': prompt_success['prompt1'],
            'prompt2': prompt_success['prompt2'],
            'prompt3': prompt_success['prompt3'],
            'prompt4': prompt_success['prompt4'],
        }
        result['verilog_diff'] = verilog_diff_text
        return result

    def _handle_diff_not_found(self, data, generated_diff, last_error_msg, verilog_diff_text, chisel_original):
        """
        On Apply_diff verification failure, retry up to 4× using prompt_diff_not_found.
        Increase metadata_context by 5 each retry.
        Returns (chisel_updated, new_generated_diff, was_valid_apply).
        was_valid_apply=True means apply_diff succeeded—verification still happens in main loop.
        """

        cfg = self.template_config.template_dict.get('v2chisel_pass1', {})
        prompt_section = cfg.get('prompt_diff_not_found')
        if not prompt_section:
            self.error("Missing 'prompt_diff_not_found' under v2chisel_pass1 in config")

        base_ctx = self.input_data.get('metadata_context', 10)

        for retry in range(1, 5):
            # bump context
            self.input_data['metadata_context'] = base_ctx + retry * 20

            # setup LLM
            tmpl = LLM_template(prompt_section)
            self.lw.name = f'v2chisel_pass1_diff_not_found_{retry}'
            self.lw.chat_template = tmpl

            # extract hints with larger context
            chisel_original = data.get('chisel_original', '')
            new_hints = self._extract_chisel_subset(chisel_original, verilog_diff_text)
            

            payload = {
                'generate_diff': generated_diff,
                'applier_error': last_error_msg,
                'new_hints':     new_hints,
                'verilog_diff': verilog_diff_text,
            }
            resp = self.lw.inference(payload,
                                     prompt_index='prompt_diff_not_found',
                                     n=5)
            prompt_str = self.lw.chat_template.format(payload)
            print('\n**** Buggy diff (prompt diff not found) ****')
            print(generated_diff)
            print('----------------------------------------------')
            print('\n========= LLM RESPONSE (prompt diff not found) =========')
            print(resp[0])
            print('==============================================')
            if not resp:
                print(f"[diff_not_found] empty response, continuing retry loop")
                continue

            # strip fences
            new_generated_diff = self._strip_markdown_fences(resp[0])

            # try apply again
            # apply with ChiselDiffApplier
            applier = ChiselDiffApplier()
            
            try:
                chisel_updated = applier.apply_diff(new_generated_diff, chisel_original)
                print('Applied the diff via ChiselDiffApplier.')
                data['chisel_candidate'] = chisel_updated
            except Exception as e:
                last_error_msg = str(e)
                print(f"[diff_not_found] apply_diff failed: {last_error_msg}")
                continue
            
            return chisel_updated, new_generated_diff, True

        # all retries failed to apply
        self.input_data['metadata_context'] = base_ctx
        print("After 5 iterations over Prompt_diff_not_found llm could not generate correct code!")
        return None, new_generated_diff, False


def wrap_literals(obj):
    if isinstance(obj, dict):
        return {k: wrap_literals(v) for k, v in obj.items()}
    elif isinstance(obj, list):
        return [wrap_literals(elem) for elem in obj]
    elif isinstance(obj, str) and '\n' in obj:
        return LiteralScalarString(obj)
    else:
        return obj


def parse_arguments():
    parser = argparse.ArgumentParser()
    # The -o flag is required for the output file
    parser.add_argument('-o', required=True, help='Output YAML file')
    parser.add_argument('-fz', '--force-fuzzy', action='store_true', dest='force_fuzzy', help='Force fuzzy-grep hints first')
    # Add a positional argument for the input file
    parser.add_argument('input_file', help='Input YAML file')
    return parser.parse_args()


if __name__ == '__main__':  # pragma: no cover
    args = parse_arguments()
    step = V2Chisel_pass1()
    step.parse_arguments()
    # propagate force-fuzzy flag to the step
    step.force_fuzzy = args.force_fuzzy
    step.setup()
    result = step.step()  # this returns your result dictionary

    result = wrap_literals(result)

    yaml = YAML()
    yaml.default_flow_style = False  # use block style formatting
    yaml.indent(mapping=2, sequence=4, offset=2)

    with open(args.o, 'w') as out_file:
        yaml.dump(result, out_file)