#!/usr/bin/env python3
# See LICENSE for details

from hagent.inou.runner import Runner
from hagent.core.step import Step
from typing import Dict
import os
import time


class ExtractRTL(Step):
    def setup(self):
        super().setup()
        # Runner setup will be done in run() after loading config

    def run(self, data: Dict):
        data_copy = data.copy()
        start_time = time.time()

        # Extract configuration from input YAML
        benchmark = data_copy.get('benchmark', {})
        docker_config = data_copy.get('docker', {})
        local_storage = data_copy.get('local_storage', {})

        # Setup runner with docker image from config
        if os.getenv('HAGENT_EXECUTION_MODE') == 'docker':
            docker_image = docker_config.get('image', 'mascucsc/hagent-simplechisel:2025.08')
            self.runner = Runner(docker_image=docker_image)
        else:
            self.runner = Runner()

        if not self.runner.setup():
            self.error(f'OOPS in step_01_extract_rtl.py error from runner:{self.runner.get_error()}')
            return data_copy

        # Create debug directory using HAGENT_CACHE_DIR for execution metadata only
        cache_dir = os.getenv('HAGENT_CACHE_DIR', local_storage.get('debug_base_dir', '/tmp/rtl_optimization_debug'))
        timestamp = str(int(time.time()))
        step_debug_dir = f"{cache_dir}/step01_extract_rtl_{timestamp}"
        os.makedirs(step_debug_dir, exist_ok=True)

        step_results = {
            'start_time': start_time,
            'debug_directory': step_debug_dir,
            'timestamp': timestamp
        }

        # Get paths from config
        rtl_path = docker_config.get('rtl_path')
        chisel_path = docker_config.get('chisel_path')

        if not rtl_path:
            self.error("RTL path not specified in docker config")
            return data_copy

        # List Chisel source files (if chisel_path is provided)
        if chisel_path:
            ret, out, err = self.runner.run(f'find {chisel_path} -name "*.scala" 2>/dev/null || echo "No Chisel files found"')
            step_results['chisel_discovery'] = {
                'ret': ret, 'stdout': out, 'stderr': err,
                'files_found': [f.strip() for f in out.split('\n') if f.strip() and not f.startswith('No Chisel')] if out else []
            }
        else:
            step_results['chisel_discovery'] = {
                'ret': 0, 'stdout': '', 'stderr': '',
                'files_found': []
            }

        # List generated Verilog files
        ret, out, err = self.runner.run(f'find {rtl_path} -name "*.v" -o -name "*.sv" 2>/dev/null || echo "No RTL files found"')
        rtl_files = [f.strip() for f in out.split('\n') if f.strip() and not f.startswith('No RTL')] if out else []
        step_results['rtl_discovery'] = {
            'ret': ret, 'stdout': out, 'stderr': err,
            'files_found': rtl_files
        }

        # Get detailed listing of RTL directory
        ret, out, err = self.runner.run(f'ls -la {rtl_path}/ 2>/dev/null || echo "Directory not found"')
        step_results['rtl_directory_listing'] = {
            'ret': ret, 'stdout': out, 'stderr': err
        }

        # Store execution metadata locally for debugging
        debug_log = f"{step_debug_dir}/execution_log.txt"
        with open(debug_log, 'w') as f:
            f.write(f"Step 01 - Extract RTL\n")
            f.write(f"Execution Time: {time.time() - start_time:.2f}s\n")
            f.write(f"Benchmark: {benchmark.get('name', 'Unknown')}\n")
            f.write(f"Top Module: {benchmark.get('top_module', 'Unknown')}\n")
            f.write(f"Docker Image: {docker_config.get('image', 'Unknown')}\n")
            f.write(f"RTL Path: {rtl_path}\n")
            f.write(f"Chisel Path: {chisel_path or 'Not specified'}\n")
            f.write(f"RTL Files Found: {len(rtl_files)}\n")
            f.write(f"Files: {rtl_files}\n")

        # Update data structure
        if 'file_paths' not in data_copy:
            data_copy['file_paths'] = {}
        data_copy['file_paths']['rtl_files'] = rtl_files
        data_copy['file_paths']['chisel_files'] = step_results['chisel_discovery']['files_found']

        # Store execution time and results
        step_results['execution_time'] = time.time() - start_time
        step_results['files_extracted'] = len(rtl_files)

        if 'step_results' not in data_copy:
            data_copy['step_results'] = {}
        data_copy['step_results']['step_01_extract_rtl'] = step_results

        # Initialize metrics if not present
        if 'metrics' not in data_copy:
            data_copy['metrics'] = {}
        if not data_copy['metrics'].get('start_time'):
            data_copy['metrics']['start_time'] = start_time

        return data_copy


if __name__ == '__main__':
    extract_rtl_step = ExtractRTL()
    extract_rtl_step.parse_arguments()
    extract_rtl_step.setup()
    extract_rtl_step.step()
