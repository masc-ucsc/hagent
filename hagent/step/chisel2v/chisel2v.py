#!/usr/bin/env python3
# See LICENSE for details

import os
import re
from hagent.core.step import Step
from hagent.core.llm_template import LLM_template
from hagent.core.llm_wrap import LLM_wrap

class Chisel2V(Step):
    def setup(self):
        """
        Read input data, load LLM prompt, and prepare the LLM wrapper.
        """
        super().setup()  # Reads input_data from the YAML

        # 1) Check that we have 'llm' config
        if 'llm' not in self.input_data:
            self.error("Missing 'llm' section in input file")

        # 2) Load the prompt file
        prompt_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'chisel2v_prompt.yaml')
        prompt_template = LLM_template(prompt_file)

        # 3) Create the LLM wrapper
        llm_args = self.input_data['llm']
        self.lw = LLM_wrap()
        self.lw.from_dict(name='chisel2v_pass', conf_dict=llm_args, prompt=prompt_template)

        self.setup_called = True

    def run(self, data):
        if "original_chisel" not in data or "modified_verilog" not in data:
            self.error("Missing original_chisel or modified_verilog in the input YAML")

        original_chisel  = data.get('original_chisel', '')
        modified_verilog = data.get('modified_verilog', '')
        module_name      = data.get('name', 'updated_chisel')

        # Create folder
        os.makedirs(module_name, exist_ok=True)
        out_path = os.path.join(module_name, f"{module_name}.scala")

        # Prepare prompt data
        prompt_dict = {
            'original_chisel':  original_chisel,
            'modified_verilog': modified_verilog
        }

        # Call the LLM
        result_list = self.lw.inference(prompt_dict, n=1)
        if not result_list:
            self.error("LLM returned an empty response")

        updated_chisel_code = result_list[0]

        # Remove triple backticks, e.g. ```scala
        updated_chisel_code = re.sub(r'```[a-zA-Z]*', '', updated_chisel_code)
        updated_chisel_code = updated_chisel_code.replace('```', '').strip()

        # Write to file
        with open(out_path, 'w', encoding='utf-8') as f:
            f.write(updated_chisel_code)

        # Prepare final output
        result = data.copy()
        result['updated_chisel'] = updated_chisel_code
        result['chisel_file']    = out_path
        return result

if __name__ == '__main__':  # pragma: no cover
    pass_obj = Chisel2V()
    pass_obj.parse_arguments()
    pass_obj.setup()
    pass_obj.step()
