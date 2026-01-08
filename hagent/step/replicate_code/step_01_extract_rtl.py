#!/usr/bin/env python3
# See LICENSE for details

from typing import Dict
import time
import os
import shutil


from hagent.step.replicate_code.schema import PipelineConfig
from hagent.step.replicate_code.opt_pipe_step_base import OptPipeStepBase


class ExtractRTL(OptPipeStepBase):
    """Extract the RTL original source code to the working directory."""
    def __init__(self):
        super().__init__()
        self.step_name = 'step_01_extract_rtl'

    def setup(self):
        super().setup()
        # Runner setup will be done in run() after loading config

    def run(self, data: Dict) -> Dict:
        # Parse input dictionary into typed configuration
        self.config = PipelineConfig.from_dict(data)

        self.prepare_environment(self.config, self.step_name)
        assert self.runner is not None  # to get rid of linting errors when invoking `self.runner.run_cmd` below

        # Access configuration via typed fields
        rtl_source_file_path = self.config.source_file_paths.rtl_source_file_path
        chisel_path = self.config.source_file_paths.chisel_path

        if not rtl_source_file_path:
            self.error('RTL source code directory not specified in config')

        # List Chisel source files (if chisel_path is provided)
        if chisel_path:
            self.logger.info(f'Discovering Chisel source files in {chisel_path}')
            ret, out, err = self.runner.run_cmd(
                f'find {chisel_path} -name "*.scala" 2>/dev/null || echo "No Chisel files found"', quiet=True
            )
            self.step_results['chisel_discovery'] = {
                'ret': ret,
                'stdout': out,
                'stderr': err,
                'files_found': [f.strip() for f in out.split('\n') if f.strip() and not f.startswith('No Chisel')] if out else [],
            }
        else:
            self.step_results['chisel_discovery'] = {'ret': 0, 'stdout': '', 'stderr': '', 'files_found': []}

        # Get detailed listing of RTL directory
        self.logger.info(f'Listing RTL source directory: {rtl_source_file_path}')
        ret, out, err = self.runner.run_cmd(
            f'ls -la {rtl_source_file_path}/ 2>/dev/null || echo "Directory not found"', quiet=True
        )
        self.step_results['rtl_directory_listing'] = {'ret': ret, 'stdout': out, 'stderr': err}

        # List generated Verilog files
        self.logger.info('Discovering Verilog/SystemVerilog files')
        ret, out, err = self.runner.run_cmd(
            f'find {rtl_source_file_path} -name "*.v" -o -name "*.sv" 2>/dev/null || echo "No RTL files found"',
            quiet=True,
        )
        rtl_source_files = [f.strip() for f in out.split('\n') if f.strip() and not f.startswith('No RTL')] if out else []
        self.step_results['rtl_discovery'] = {'ret': ret, 'stdout': out, 'stderr': err, 'files_found': rtl_source_files}

        rtl_real_src_dir = os.path.join(self.work_dir, 'rtl_real_source')
        self._prepare_dir(rtl_real_src_dir)

        rtl_modules_path = os.path.join(self.work_dir, 'rtl_modules')
        self._prepare_dir(rtl_modules_path)

        self.logger.info(f'Copying {len(rtl_source_files)} RTL files to {rtl_real_src_dir}')
        for src_file in rtl_source_files:
            if os.path.isfile(src_file):
                real_src_dst_file = os.path.join(rtl_real_src_dir, os.path.basename(src_file))
                submodules_dst_file = os.path.join(rtl_modules_path, os.path.basename(src_file))
                shutil.copy2(src_file, real_src_dst_file)
                shutil.copy2(src_file, submodules_dst_file)

        # Store execution metadata locally for debugging
        debug_log = f'{self.step_debug_dir}/execution_log.txt'
        self.logger.info(f'Writing debug log to {debug_log}')
        with open(debug_log, 'w') as f:
            f.write('Step 01 - Extract RTL\n')
            f.write(f'Execution Time: {time.time() - self.start_time:.2f}s\n')
            f.write(f'Benchmark: {self.config.benchmark.name}\n')
            f.write(f'Top Module: {self.config.benchmark.top_module}\n')
            f.write(f'Docker Image: {self.config.docker.image if self.config.docker else "Not specified"}\n')
            f.write(f'RTL Real Source Directory: {rtl_real_src_dir}\n')
            f.write(f'Chisel Path: {chisel_path or "Not specified"}\n')
            f.write(f'RTL Files Found: {len(rtl_source_files)}\n')
            f.write(f'Files: {rtl_source_files}\n')

        # Update populated file paths in the working directory in config
        self.config.populated_file_paths.rtl_real_src_dir = rtl_real_src_dir
        self.config.populated_file_paths.rtl_path = rtl_modules_path
        self.config.populated_file_paths.chisel_files = self.step_results['chisel_discovery']['files_found']

        # Store execution time and results
        self.step_results['execution_time'] = time.time() - self.start_time
        self.step_results['files_extracted'] = len(rtl_real_src_dir)

        # Save step results to file and store reference in config
        results_file = self.save_step_results()
        self.config.step_results[self.step_name] = {'results_file': results_file}

        # Initialize metrics if not present
        if not self.config.metrics.start_time:
            self.config.metrics.start_time = self.start_time
        if not self.config.metrics.end_time:
            self.config.metrics.end_time = time.time()

        # Convert back to dict for pipeline compatibility
        return self.config.to_dict()


if __name__ == '__main__':
    extract_rtl_step = ExtractRTL()
    extract_rtl_step.parse_arguments()
    extract_rtl_step.setup()
    extract_rtl_step.step()
