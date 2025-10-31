#!/usr/bin/env python3
# See LICENSE for details

from hagent.inou.runner import Runner
from hagent.core.step import Step
from typing import Dict
import os
import time


class SplitModules(Step):
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
            self.error(f'OOPS in step_03_split_modules.py error from runner:{self.runner.get_error()}')
            return data_copy

        # Create debug directory
        cache_dir = os.getenv('HAGENT_CACHE_DIR', local_storage.get('debug_base_dir', '/tmp/rtl_optimization_debug'))
        timestamp = str(int(time.time()))
        step_debug_dir = f"{cache_dir}/step03_split_modules_{timestamp}"
        os.makedirs(step_debug_dir, exist_ok=True)

        step_results = {
            'start_time': start_time,
            'debug_directory': step_debug_dir,
            'timestamp': timestamp
        }

        # Get configuration
        top_module_file = data_copy.get('file_paths', {}).get('top_module_file')
        livehd_path = tools.get('livehd_path', '~/livehd/')

        if not top_module_file:
            self.error("Top module file not found in previous step results")
            return data_copy

        # Create rtl_modules directory
        rtl_modules_path = '/tmp/rtl_modules'
        ret, out, err = self.runner.run(f'rm -rf {rtl_modules_path} && mkdir -p {rtl_modules_path}')
        step_results['directory_setup'] = {
            'ret': ret, 'stdout': out, 'stderr': err
        }

        # Change to livehd directory and build
        ret, out, err = self.runner.run(f'cd {livehd_path} && bazel build -c opt //...')
        step_results['livehd_build'] = {
            'ret': ret, 'stdout': out, 'stderr': err
        }

        if ret != 0:
            self.error(f"LiveHD build failed: {err}")
            return data_copy

        # Clean lgdb if it exists
        ret, out, err = self.runner.run(f'cd {livehd_path} && rm -rf lgdb/')
        step_results['lgdb_cleanup'] = {
            'ret': ret, 'stdout': out, 'stderr': err
        }

        # Run LiveHD liveparse to split modules
        lgshell_cmd = f'cd {livehd_path} && ./bazel-bin/main/lgshell "inou.liveparse files:{top_module_file} path:{rtl_modules_path}"'
        ret, out, err = self.runner.run(lgshell_cmd)
        step_results['liveparse_execution'] = {
            'ret': ret, 'stdout': out, 'stderr': err,
            'command': lgshell_cmd
        }

        if ret != 0:
            self.error(f"LiveHD liveparse failed: {err}")
            return data_copy

        # List the generated modules
        ret, out, err = self.runner.run(f'find {rtl_modules_path} -name "*.v" | sort')
        split_modules = [f.strip() for f in out.split('\n') if f.strip()] if out else []
        step_results['modules_generated'] = {
            'ret': ret, 'stdout': out, 'stderr': err,
            'module_files': split_modules
        }

        # Get detailed listing
        ret, out, err = self.runner.run(f'ls -la {rtl_modules_path}/liveparse/')
        step_results['liveparse_directory_listing'] = {
            'ret': ret, 'stdout': out, 'stderr': err
        }

        # Store execution metadata locally for debugging
        debug_log = f"{step_debug_dir}/execution_log.txt"
        with open(debug_log, 'w') as f:
            f.write(f"Step 03 - Split Modules with LiveHD\n")
            f.write(f"Execution Time: {time.time() - start_time:.2f}s\n")
            f.write(f"Benchmark: {benchmark.get('name', 'Unknown')}\n")
            f.write(f"Input File: {top_module_file}\n")
            f.write(f"Output Directory: {rtl_modules_path}\n")
            f.write(f"LiveHD Path: {livehd_path}\n")
            f.write(f"LiveHD Build Return Code: {step_results['livehd_build']['ret']}\n")
            f.write(f"Liveparse Return Code: {step_results['liveparse_execution']['ret']}\n")
            f.write(f"Modules Generated: {len(split_modules)}\n")
            f.write(f"Module Files: {split_modules}\n")

        # Update file paths
        if 'file_paths' not in data_copy:
            data_copy['file_paths'] = {}
        data_copy['file_paths']['rtl_modules_dir'] = rtl_modules_path
        data_copy['file_paths']['split_module_files'] = split_modules

        # Store execution time and results
        step_results['execution_time'] = time.time() - start_time
        step_results['modules_count'] = len(split_modules)
        step_results['success'] = (ret == 0 and len(split_modules) > 0)

        if 'step_results' not in data_copy:
            data_copy['step_results'] = {}
        data_copy['step_results']['step_03_split_modules'] = step_results

        return data_copy


if __name__ == '__main__':
    split_modules_step = SplitModules()
    split_modules_step.parse_arguments()
    split_modules_step.setup()
    split_modules_step.step()