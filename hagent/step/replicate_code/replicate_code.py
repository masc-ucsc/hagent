#!/usr/bin/env python3
# See LICENSE for details

import os
from hagent.core.step import Step
from hagent.core.llm_wrap import LLM_wrap
from hagent.core.llm_template import LLM_template


class Replicate_code(Step):
    def setup(self):
        super().setup()  # superclass

        llm_args = {}
        if 'llm' in self.input_data:
            llm_args = self.input_data['llm']
        else:
            self.error(f'llm arguments not set in input file {self.input_file}')

        self.setup_called = True
        templ_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'prompt1.yaml')

        templ = LLM_template(templ_file)

        txt = templ.format({'code': 'potato'})
        print(f'templ{txt}')

        self.lw = LLM_wrap()
        self.lw.from_dict(name='replicate_code', conf_dict=llm_args, prompt=templ)

    def run(self, data):
        code = data['code']

        print(f'code:{code}')

        res = self.lw.inference({'code': code}, n=2)

        # res_code = self.filter_markdown_snippet(res)

        result = data.copy()
        result['optimized'] = res

        assert len(res) == 2

        return result


if __name__ == '__main__':  # pragma: no cover
    rep_step = Replicate_code()
    rep_step.parse_arguments()  # or rep_step.set_io(...)
    rep_step.setup()
    rep_step.step()
