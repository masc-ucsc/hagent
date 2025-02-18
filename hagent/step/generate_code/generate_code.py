#!/usr/bin/env python3
# See LICENSE for details

import os
import re
from hagent.core.step import Step
from hagent.core.llm_wrap import LLM_wrap
from hagent.core.llm_template import LLM_template


class Generate_code(Step):
    def setup(self):
        super().setup()  # superclass

        extra_config_args = self.input_data['generate_code']

        if not 'llm' in extra_config_args:
            self.error(f'generate_code.llm arguments not set in input file {self.input_file}')

        self.setup_called = True
        conf_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'prompt1.yaml')

        self.lw = LLM_wrap(name='generate_code', conf_file=conf_file, log_file="generate_code.log", overwrite_conf=extra_config_args)

        self.setup_called = True

    def run(self, data):
        # description = data['description']
        description = data.get('description', '')
        interface = data.get('interface', '')
        bench_response = data.get('bench_response', '')
        bench_stage = data.get('bench_stage', '')
        module_name = data.get('name', 'default_module')

        print(f"[INFO] Generating code for module '{module_name}'")
        print(f'[INFO] Description:\n{description}')
        print(f'[INFO] Interface:\n{interface}')
        print(f'[INFO] Bench response:\n{bench_response}')
        print(f'[INFO] Bench stage: {bench_stage}')

        os.makedirs(module_name, exist_ok=True)
        verilog_path = os.path.join(module_name, f'{module_name}.v')

        # res = self.lw.inference({'description': description})
        prompt_dict = {'description': description, 'interface': interface}
        llm_response_list = self.lw.inference(prompt_dict)
        if not llm_response_list:
            self.error('LLM returned an empty response.')
        # res_code = self.filter_markdown_snippet(res)
        generated_code_str = llm_response_list[0]

        generated_code_str = re.sub(r'```[a-zA-Z]*', '', generated_code_str)  # remove ```verilog or ```python
        generated_code_str = generated_code_str.replace('```', '').strip()

        with open(verilog_path, 'w', encoding='utf-8') as f:
            f.write(generated_code_str)

        print(f'[INFO] Verilog written to: {verilog_path}')

        result = data.copy()
        # result['generated_code'] = res
        result['generated_code'] = llm_response_list  # store all responses if you want
        result['verilog_file'] = verilog_path
        # Just keep bench_response/bench_stage if you want them in final YAML
        # You can also transform them or do something else with them
        result['bench_response'] = bench_response
        result['bench_stage'] = bench_stage

        return result
        # assert len(res) == 2


if __name__ == '__main__':  # pragma: no cover
    rep_step = Generate_code()
    rep_step.parse_arguments()  # or rep_step.set_io(...)
    rep_step.setup()
    rep_step.step()
