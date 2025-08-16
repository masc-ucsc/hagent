#!/usr/bin/env python3
# See LICENSE for details

from hagent.inou.executor import ExecutorFactory
from hagent.core.step import Step
from typing import Dict


# Trivial example of extending the Pass class
class Trivial(Step):
    def setup(self):
        super().setup()  # superclass
        self.executor = ExecutorFactory.create_executor()
        if not self.executor.setup():
            self.set_error(f'OOPS in trivial.py error fror executor:{self.executor.get_error()}')

    def run(self, data: Dict):
        data_copy = data.copy()
        data_copy['added_field_trivial'] = 'sample'

        ret, out, err = self.executor.run('uname -a')
        data_copy['uname_ret'] = str(ret)
        data_copy['uname_out'] = out
        data_copy['uname_err'] = err

        ret, out, err = self.executor.run('pwd')
        data_copy['pwd_ret'] = str(ret)
        data_copy['pwd_out'] = out
        data_copy['pwd_err'] = err

        ret, out, err = self.executor.run('which yosys')
        data_copy['yosys_path_ret'] = str(ret)
        data_copy['yosys_path_out'] = out
        data_copy['yosys_path_err'] = err

        # Simply return the input data without modification
        return data_copy


if __name__ == '__main__':  # pragma: no cover
    trivial_step = Trivial()
    trivial_step.parse_arguments()
    trivial_step.setup()
    trivial_step.step()
