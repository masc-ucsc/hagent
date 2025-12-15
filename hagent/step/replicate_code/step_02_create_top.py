#!/usr/bin/env python3
# See LICENSE for details

from typing import Dict
import time
import os

from hagent.step.replicate_code.schema import PipelineConfig
from hagent.step.replicate_code.opt_pipe_step_base import OptPipeStepBase


class CreateTop(OptPipeStepBase):
    """
    Use Yosys to elaborate and isolate the chosen top-level module from the original RTL source files generated and write it as a clean single-file design (rtl_single) to prepare for synthesis.
    Example of what this function does: top.v(rtl)--{yosys}-->rtl_single/pipelinedCPU.v(rtl) 
    """
    def __init__(self):
        super().__init__()
        self.step_name = 'step_02_create_top'

    def setup(self):
        super().setup()

    def run(self, data: Dict) -> Dict:
        # Parse input dictionary into typed configuration
        self.config = PipelineConfig.from_dict(data)

        self.prepare_environment(self.config, self.step_name)
        assert self.runner is not None

        # Access configuration via typed fields
        top_module = self.config.benchmark.top_module
        yosys_cmd = self.config.tools.yosys_cmd

        if not top_module:
            self.error('RTL top module not specified in config')

        # Create directories in docker
        rtl_selected_top_path = os.path.join(self.work_dir, 'rtl_single')
        os.makedirs(rtl_selected_top_path, exist_ok=True)

        # Create top module file using Yosys
        rtl_selected_top_file = os.path.join(rtl_selected_top_path, f'{top_module}.v')
        yosys_script = f"""
            read_verilog -sv -defer {self.config.populated_file_paths.rtl_real_src_dir}/*;
            hierarchy -top {top_module};
            write_verilog {rtl_selected_top_file};
        """

        self.logger.info(f'Creating top module using Yosys: {top_module}')
        ret, out, err = self.runner.run_cmd(f'{yosys_cmd} -p "{yosys_script}"', quiet=True)
        self.step_results['yosys_execution'] = {
            'ret': ret,
            'stdout': out,
            'stderr': err,
            'command': f'{yosys_cmd} -p "{yosys_script}"',
        }

        if ret != 0:
            self.logger.error('Yosys failed to create top module!')
            self.logger.error(f'Return code: {ret}')
            self.logger.error(f'STDOUT:\n{out}')
            self.logger.error(f'STDERR:\n{err}')
            self.error(f'Yosys failed to create top module: {err}')

        # Verify the file was created
        self.logger.info(f'Verifying created file: {rtl_selected_top_file}')
        ret, out, err = self.runner.run_cmd(f'ls -la {rtl_selected_top_file}', quiet=True)
        self.step_results['file_verification'] = {'ret': ret, 'stdout': out, 'stderr': err}

        # Get file stats for debugging
        ret, out, err = self.runner.run_cmd(f'wc -l {rtl_selected_top_file}', quiet=True)
        self.step_results['file_stats'] = {'ret': ret, 'stdout': out, 'stderr': err}

        # Store execution metadata locally for debugging
        debug_log = f'{self.step_debug_dir}/execution_log.txt'
        self.logger.debug(f'Writing debug log to {debug_log}')
        with open(debug_log, 'w') as f:
            f.write('Step 02 - Create Top Module\n')
            f.write(f'Execution Time: {time.time() - self.start_time:.2f}s\n')
            f.write(f'Benchmark: {self.config.benchmark.name}\n')
            f.write(f'Top Module: {top_module}\n')
            f.write(f'RTL Real Source Directory: {self.config.populated_file_paths.rtl_real_src_dir}\n')
            f.write(f'Output File: {rtl_selected_top_file}\n')
            f.write(f'Yosys Command: {yosys_cmd}\n')
            f.write(f'Yosys Return Code: {self.step_results["yosys_execution"]["ret"]}\n')
            if self.step_results['yosys_execution']['ret'] == 0:
                f.write('File Created Successfully\n')
            else:
                f.write(f'Error: {self.step_results["yosys_execution"]["stderr"]}\n')

        # Update populated file paths in config
        self.config.populated_file_paths.rtl_selected_top_path = rtl_selected_top_path

        # Store execution time and results
        self.step_results['execution_time'] = time.time() - self.start_time
        self.step_results['success'] = ret == 0

        # Save step results to file and store reference in config
        results_file = self.save_step_results()
        self.config.step_results[self.step_name] = {'results_file': results_file}

        # Convert back to dict for pipeline compatibility
        return self.config.to_dict()


if __name__ == '__main__':
    create_top_step = CreateTop()
    create_top_step.parse_arguments()
    create_top_step.setup()
    create_top_step.step()
