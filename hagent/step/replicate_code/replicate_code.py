#!/usr/bin/env python3
# See LICENSE for details

import os
from hagent.core.step import Step
from hagent.core.llm_wrap import LLM_wrap

from hagent.tool.extract_code import Extract_code_default


class Replicate_code(Step):
    def setup(self):
        super().setup()  # superclass
        print(f"input_file:{self.input_file}")

        self.extractor = Extract_code_default()

        self.setup_called = True
        conf_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'prompt1.yaml')

        self.lw = LLM_wrap(name='replicate_code', log_file="replicate_code.log", conf_file=conf_file, overwrite_conf=self.input_data)

        if self.lw.last_error:
            raise ValueError(self.lw.last_error)

    def run(self, data):
        code = data['code']

        print(f'code:{code}')

        res = self.lw.inference({'code': code}, "replicate_code_prompt1", n=2)

        result = data.copy()

        for markdown in res:
            code = self.extractor.parse(markdown)
            if code:
                result['optimized'] = code

        return result


if __name__ == '__main__':  # pragma: no cover
    rep_step = Replicate_code()
    rep_step.parse_arguments()  # or rep_step.set_io(...)
    rep_step.setup()
    rep_step.step()
