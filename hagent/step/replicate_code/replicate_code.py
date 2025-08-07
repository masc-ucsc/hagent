#!/usr/bin/env python3
# See LICENSE for details

import os
import sys
import time
from hagent.core.step import Step
from hagent.core.llm_wrap import LLM_wrap
from hagent.tool.equiv_check import Equiv_check
from hagent.tool.extract_code import Extract_code_verilog
from hagent.core.output_manager import get_output_dir


class Replicate_code(Step):
    def setup(self):
        super().setup()  # superclass
        # print(f"input_file:{self.input_file}")

        self.verilog_extractor = Extract_code_verilog()

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
        # print('-----------------code_content:------------------')

        # print(f'code:{original_code}')

        res = self.lw.inference({'code_content': original_code}, 'replicate_code_prompt1', n=5)  # n=2 means it will give me 2 answers
        # print("--------res:-----\n")
        # print(res)
        # print('\n\n\n')

        result = data.copy()

        result['optimized'] = []  # Store all markdowns in a list
        for markdown in res:
            codes = self.verilog_extractor.parse(markdown)
            for new_code in codes:
                if new_code:
                    # Normalize whitespace for comparison to avoid including identical code with different spacing
                    normalized_new = ' '.join(new_code.split())
                    normalized_original = ' '.join(original_code.split())
                    if normalized_new != normalized_original:
                        result['optimized'].append(new_code)

        # print(f'\n\n\n result => \n\n {data} \n\n')
        codes_passing_lec = self.check_lec(result)
        result['optimized_equivalent'] = codes_passing_lec

        x = 1
        # get the optimized code from result and save it in output directory
        output_dir = get_output_dir()
        for markdown in codes_passing_lec:
            optimized_vers = self.verilog_extractor.parse(markdown)
            for optimized_ver in optimized_vers:
                if optimized_ver:
                    # filename = os.path.join(output_dir , f'{data['top_name']}_optimized_{x}.v')
                    filename = os.path.join(output_dir, f'option_{x}.v')
                    x += 1
                    os.makedirs(os.path.dirname(filename), exist_ok=True)
                    with open(filename, 'w') as f:
                        f.write(optimized_ver)

        return result


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
