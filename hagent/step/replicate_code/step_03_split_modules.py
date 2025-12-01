#!/usr/bin/env python3
# See LICENSE for details

from typing import Dict
import time
import os

from hagent.step.replicate_code.schema import PipelineConfig
from hagent.step.replicate_code.opt_pipe_step_base import OptPipeStepBase


class SplitModules(OptPipeStepBase):
    """
    Example of what this function does: pipelinedCPU.v(rtl)---{liveHD}--->rtl_modules/ control.v, alu.v, PipelinedCPU.v, etc. (rtl)
    """
    def __init__(self):
        super().__init__()
        self.step_name = 'step_03_split_modules'

    def setup(self):
        super().setup()

    def _run_impl(self, data: Dict):
        # Parse input dictionary into typed configuration
        config = PipelineConfig.from_dict(data)

        self.prepare_environment(config, self.step_name)
        assert self.runner is not None

        # Access configuration via typed fields
        top_module_path = config.populated_file_paths.rtl_selected_top_path
        if not top_module_path or not os.path.isdir(top_module_path):
            self.error(f'Top module directory not found: {top_module_path}')

        top_module_file = f'{top_module_path}/{config.benchmark.top_module}.v'
        config.populated_file_paths.rtl_selected_top_file = top_module_file
        livehd_path = config.tools.livehd_path

        # Create rtl_modules directory
        rtl_modules_path = os.path.join(self.work_dir, 'rtl_modules')
        self._prepare_dir(rtl_modules_path)

        # Change to livehd directory and build
        self.logger.info('Building LiveHD with Bazel')
        ret, out, err = self.runner.run_cmd(f'cd {livehd_path} && bazel build -c opt //...', quiet=True)
        self.step_results['livehd_build'] = {'ret': ret, 'stdout': out, 'stderr': err}

        if ret != 0:
            self.logger.error('LiveHD build failed!')
            self.logger.error(f'Return code: {ret}')
            self.logger.error(f'STDOUT:\n{out}')
            self.logger.error(f'STDERR:\n{err}')
            self.error(f'LiveHD build failed: {err}')

        # Clean lgdb if it exists
        self.logger.info('Cleaning lgdb directory')
        ret, out, err = self.runner.run_cmd(f'cd {livehd_path} && rm -rf lgdb/', quiet=True)
        self.step_results['lgdb_cleanup'] = {'ret': ret, 'stdout': out, 'stderr': err}

        # Run LiveHD liveparse to split modules
        self.logger.info(f'Running liveparse on {top_module_file}')
        lgshell_cmd = (
            f'cd {livehd_path} && ./bazel-bin/main/lgshell "inou.liveparse files:{top_module_file} path:{rtl_modules_path}"'
        )
        ret, out, err = self.runner.run_cmd(lgshell_cmd, quiet=True)
        self.step_results['liveparse_execution'] = {'ret': ret, 'stdout': out, 'stderr': err, 'command': lgshell_cmd}

        if ret != 0:
            self.logger.error('LiveHD liveparse failed!')
            self.logger.error(f'Return code: {ret}')
            self.logger.error(f'STDOUT:\n{out}')
            self.logger.error(f'STDERR:\n{err}')
            self.error(f'LiveHD liveparse failed: {err}')

        # List the generated modules
        self.logger.info('Listing generated module files')
        ret, out, err = self.runner.run_cmd(f'find {rtl_modules_path} -name "*.v" | sort', quiet=True)
        split_modules = [f.strip() for f in out.split('\n') if f.strip()] if out else []
        self.step_results['modules_generated'] = {'ret': ret, 'stdout': out, 'stderr': err, 'module_files': split_modules}

        # Get detailed listing
        ret, out, err = self.runner.run_cmd(f'ls -la {rtl_modules_path}/liveparse/', quiet=True)
        self.step_results['liveparse_directory_listing'] = {'ret': ret, 'stdout': out, 'stderr': err}

        self.logger.info(f'Generated {len(split_modules)} module files')

        # Store execution metadata locally for debugging
        debug_log = f'{self.step_debug_dir}/execution_log.txt'
        self.logger.info(f'Writing debug log to {debug_log}')
        with open(debug_log, 'w') as f:
            f.write('Step 03 - Split Modules with LiveHD\n')
            f.write(f'Execution Time: {time.time() - self.start_time:.2f}s\n')
            f.write(f'Benchmark: {config.benchmark.name}\n')
            f.write(f'Input File: {top_module_file}\n')
            f.write(f'Output Directory: {rtl_modules_path}\n')
            f.write(f'LiveHD Path: {livehd_path}\n')
            f.write(f'LiveHD Build Return Code: {self.step_results["livehd_build"]["ret"]}\n')
            f.write(f'Liveparse Return Code: {self.step_results["liveparse_execution"]["ret"]}\n')
            f.write(f'Modules Generated: {len(split_modules)}\n')
            f.write(f'Module Files: {split_modules}\n')

        # Update populated file paths in config
        config.populated_file_paths.rtl_path = rtl_modules_path

        # Store execution time and results
        self.step_results['execution_time'] = time.time() - self.start_time
        self.step_results['modules_count'] = len(split_modules)
        self.step_results['success'] = ret == 0 and len(split_modules) > 0

        # Save step results to file and store reference in config
        results_file = self.save_step_results()
        config.step_results[self.step_name] = {'results_file': results_file}

        # Convert back to dict for pipeline compatibility
        return config.to_dict()


if __name__ == '__main__':
    split_modules_step = SplitModules()
    split_modules_step.parse_arguments()
    split_modules_step.setup()
    split_modules_step.step()
