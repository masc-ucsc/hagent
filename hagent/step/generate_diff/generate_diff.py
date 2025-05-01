import os
import re
from hagent.core.step import Step
from hagent.core.llm_template import LLM_template
from hagent.core.llm_wrap import LLM_wrap

class Generate_diff(Step):
    """
    Step to run the LLM prompt loop and produce a unified diff of Chisel changes.

    Reads from:
      - verilog_diff
      - chisel_original
      - hints (chisel_subset)
    Emits:
      - generated_diff: str
    """
    def setup(self):
        super().setup()
        # point at the same YAML that v2chisel_pass1 is using
        conf_file = os.path.join(os.path.dirname(__file__),
                                 'v2chisel_pass1_conf.yaml')
        self.template_config = LLM_template(conf_file)

        # if a parent already injected self.lw, reuse it
        if not hasattr(self, 'lw') or self.lw is None:
            llm_conf = (self.template_config
                        .template_dict
                        .get('v2chisel_pass1', {})
                        .get('llm', {}))
            self.lw = LLM_wrap(
                name='v2chisel_pass1',
                log_file='generate_diff.log',
                conf_file=conf_file,
                overwrite_conf=llm_conf
            )
            if self.lw.last_error:
                raise ValueError(self.lw.last_error)

        self.setup_called = True

    def _strip_markdown_fences(self, code_str: str) -> str:
        # identical to the monolithic pass1
        code_str = re.sub(r'```[a-zA-Z]*', '', code_str)
        return code_str.replace('```', '').strip()

    def run(self, data):
        # Prepare inputs
        verilog_diff = data.get('verilog_diff', '')
        chisel_original = data.get('chisel_original', '')
        chisel_subset = data.get('hints', '')
        last_error = data.get('error_msg', '')

        # Use prompt0 for initial diff generation
        prompt_section = self.template_config.template_dict['v2chisel_pass1']['prompt0']
        prompt_template = LLM_template(prompt_section)
        self.lw.chat_template = prompt_template

        prompt_dict = {
            'verilog_diff': verilog_diff,
            'chisel_original': chisel_original,
            'chisel_subset': chisel_subset,
            'error_msg': last_error
        }

        response = self.lw.inference(prompt_dict, prompt_index='prompt0', n=1)
        if not response:
            generated = ''
        else:
            generated = self._strip_markdown_fences(response[0])

        data['generated_diff'] = generated
        return data
