#!/usr/bin/env python3
# See LICENSE for details

from hagent.inou.runner import Runner
from hagent.core.step import Step

from typing import Dict

import os


class DinoRead(Step):
    def setup(self):
        super().setup()  # superclass
        if os.getenv('HAGENT_EXECUTION_MODE') == 'docker':
            self.runner = Runner(docker_image='mascucsc/hagent-simplechisel:2025.08')
        else:
            self.runner = Runner()

        if not self.runner.setup():
            self.error(f'OOPS in dino_read.py error from runner:{self.runner.get_error()}')

    def run(self, data: Dict):
        data_copy = data.copy()
        data_copy['added_field_dino_read'] = 'dino_rtl_listing'

        # List RTL files in the docker container
        ret, out, err = self.runner.run('find /code/workspace/build/build_pipelined_d -name "*.v" -o -name "*.sv" 2>/dev/null | head -20')
        data_copy['rtl_files_ret'] = str(ret)
        data_copy['rtl_files_out'] = out
        data_copy['rtl_files_err'] = err

        # Also check for Chisel source files
        ret, out, err = self.runner.run('find /repo/src/main/scala -name "*.scala" 2>/dev/null | head -20')
        data_copy['chisel_files_ret'] = str(ret)
        data_copy['chisel_files_out'] = out
        data_copy['chisel_files_err'] = err

        # Check RTL directories structure
        ret, out, err = self.runner.run('ls -la /code/workspace/build/build_pipelined_d/ 2>/dev/null || echo "No /code/workspace/build/build_pipelined_d/ directory found"')
        data_copy['rtl_dirs_ret'] = str(ret)
        data_copy['rtl_dirs_out'] = out
        data_copy['rtl_dirs_err'] = err

        # Check for any .v files in current directory and subdirectories
        ret, out, err = self.runner.run('find . -name "*.v" | head -10')
        data_copy['local_v_files_ret'] = str(ret)
        data_copy['local_v_files_out'] = out
        data_copy['local_v_files_err'] = err

        return data_copy


if __name__ == '__main__':  # pragma: no cover
    dino_read_step = DinoRead()
    dino_read_step.parse_arguments()
    dino_read_step.setup()
    dino_read_step.step()