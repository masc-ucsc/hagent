#!/usr/bin/env python3
# See LICENSE for details

from hagent.inou.runner import Runner
from hagent.core.step import Step
from typing import Dict
import os
import time


class CreateTop(Step):
    def setup(self):
        super().setup()

    def run(self, data: Dict):
        data_copy = data.copy()
        start_time = time.time()

        # Extract configuration from input YAML
        benchmark = data_copy.get('benchmark', {})
        docker_config = data_copy.get('docker', {})
        local_storage = data_copy.get('local_storage', {})
        tools = data_copy.get('tools', {})

        # Setup runner with docker image from config
        if os.getenv('HAGENT_EXECUTION_MODE') == 'docker':
            docker_image = docker_config.get('image')
            self.runner = Runner(docker_image=docker_image)
        else:
            self.runner = Runner()

        if not self.runner.setup():
            self.error(f'OOPS in step_02_create_top.py error from runner:{self.runner.get_error()}')
            return data_copy

        # Create debug directory
        cache_dir = os.getenv('HAGENT_CACHE_DIR', local_storage.get('debug_base_dir', '/tmp/rtl_optimization_debug'))
        timestamp = str(int(time.time()))
        step_debug_dir = f"{cache_dir}/step02_create_top_{timestamp}"
        os.makedirs(step_debug_dir, exist_ok=True)

        step_results = {
            'start_time': start_time,
            'debug_directory': step_debug_dir,
            'timestamp': timestamp
        }

        # Get configuration
        rtl_path = docker_config.get('rtl_path')
        top_module = benchmark.get('top_module')
        yosys_cmd = tools.get('yosys_cmd', 'yosys')

        if not rtl_path or not top_module:
            self.error("RTL path or top module not specified in config")
            return data_copy

        # Create directories in docker
        ret, out, err = self.runner.run('mkdir -p /tmp/rtl_single')
        if ret != 0:
            self.error(f"Failed to create directory: {err}")
            return data_copy

        # Create top module file using Yosys
        rtl_selected_top_file = f"/tmp/rtl_single/{top_module}.v"
        yosys_script = f"""
            read_verilog -sv -defer {rtl_path}/*;
            hierarchy -top {top_module};
            write_verilog {rtl_selected_top_file};
        """

        ret, out, err = self.runner.run(f'{yosys_cmd} -p "{yosys_script}"')
        step_results['yosys_execution'] = {
            'ret': ret, 'stdout': out, 'stderr': err,
            'command': f'{yosys_cmd} -p "{yosys_script}"'
        }

        if ret != 0:
            self.error(f"Yosys failed to create top module: {err}")
            return data_copy

        # Verify the file was created
        ret, out, err = self.runner.run(f'ls -la {rtl_selected_top_file}')
        step_results['file_verification'] = {
            'ret': ret, 'stdout': out, 'stderr': err
        }

        # Get file stats for debugging
        ret, out, err = self.runner.run(f'wc -l {rtl_selected_top_file}')
        step_results['file_stats'] = {
            'ret': ret, 'stdout': out, 'stderr': err
        }

        # Store execution metadata locally for debugging
        debug_log = f"{step_debug_dir}/execution_log.txt"
        with open(debug_log, 'w') as f:
            f.write(f"Step 02 - Create Top Module\n")
            f.write(f"Execution Time: {time.time() - start_time:.2f}s\n")
            f.write(f"Benchmark: {benchmark.get('name', 'Unknown')}\n")
            f.write(f"Top Module: {top_module}\n")
            f.write(f"RTL Path: {rtl_path}\n")
            f.write(f"Output File: {rtl_selected_top_file}\n")
            f.write(f"Yosys Command: {yosys_cmd}\n")
            f.write(f"Yosys Return Code: {step_results['yosys_execution']['ret']}\n")
            if step_results['yosys_execution']['ret'] == 0:
                f.write(f"File Created Successfully\n")
            else:
                f.write(f"Error: {step_results['yosys_execution']['stderr']}\n")

        # Update file paths
        if 'file_paths' not in data_copy:
            data_copy['file_paths'] = {}
        data_copy['file_paths']['rtl_single_dir'] = '/tmp/rtl_single'
        data_copy['file_paths']['top_module_file'] = rtl_selected_top_file

        # Store execution time and results
        step_results['execution_time'] = time.time() - start_time
        step_results['success'] = (ret == 0)

        if 'step_results' not in data_copy:
            data_copy['step_results'] = {}
        data_copy['step_results']['step_02_create_top'] = step_results

        return data_copy


if __name__ == '__main__':
    create_top_step = CreateTop()
    create_top_step.parse_arguments()
    create_top_step.setup()
    create_top_step.step()