#!/usr/bin/env python3
# See LICENSE for details

from hagent.inou.runner import Runner
from hagent.core.step import Step
from typing import Dict
import os
import time
import re


class TimingAnalysis(Step):
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
            self.error(f'OOPS in step_05_timing_analysis.py error from runner:{self.runner.get_error()}')
            return data_copy

        # Create debug directory
        cache_dir = os.getenv('HAGENT_CACHE_DIR', local_storage.get('debug_base_dir', '/tmp/rtl_optimization_debug'))
        timestamp = str(int(time.time()))
        step_debug_dir = f"{cache_dir}/step05_timing_analysis_{timestamp}"
        os.makedirs(step_debug_dir, exist_ok=True)

        step_results = {
            'start_time': start_time,
            'debug_directory': step_debug_dir,
            'timestamp': timestamp
        }

        # Get configuration
        synth_file = data_copy.get('file_paths', {}).get('synth_file')
        sdc_file = data_copy.get('file_paths', {}).get('sdc_file')
        top_module = benchmark.get('top_module')
        liberty_file = tools.get('liberty_file')
        opensta_path = tools.get('opensta_path', '~/opensta/OpenSTA/app/sta')

        if not synth_file or not top_module or not liberty_file:
            self.error("Missing required configuration: synth_file, top_module, or liberty_file")
            return data_copy

        # Create TCL script for OpenSTA
        sta_tcl_file = "/tmp/run_sta.tcl"
        timing_report_file = "/tmp/timing_report.rpt"

        tcl_content = f"""
read_liberty {liberty_file}
set_units -time ns -capacitance pF -voltage V -current mA -resistance kOhm -distance um
set_operating_conditions ff_100C_1v95
read_verilog {synth_file}
link_design {top_module}
read_sdc {sdc_file}
report_checks -path_delay max > {timing_report_file}
"""

        ret, out, err = self.runner.run(f'cat > {sta_tcl_file} << "EOF"\n{tcl_content}\nEOF')
        step_results['tcl_creation'] = {
            'ret': ret, 'stdout': out, 'stderr': err
        }

        # Run OpenSTA
        ret, out, err = self.runner.run(f'echo "source {sta_tcl_file}" | {opensta_path}')
        step_results['opensta_execution'] = {
            'ret': ret, 'stdout': out, 'stderr': err,
            'command': f'echo "source {sta_tcl_file}" | {opensta_path}'
        }

        # Read timing report
        ret, report_content, err = self.runner.run(f'cat {timing_report_file}')
        step_results['timing_report'] = {
            'ret': ret, 'content': report_content, 'stderr': err
        }

        # Parse timing results
        arrival_time = None
        slack = None
        frequency = None

        if report_content:
            # Extract arrival time
            arrival_match = re.search(r'(\d+\.\d+)\s+data arrival time', report_content)
            if arrival_match:
                arrival_time = float(arrival_match.group(1))

            # Extract slack (may be negative)
            slack_match = re.search(r'(-?\d+\.\d+)\s+slack', report_content)
            if slack_match:
                slack = float(slack_match.group(1))

            # Calculate frequency if we have arrival time
            if arrival_time and arrival_time > 0:
                frequency = 1000.0 / arrival_time  # Convert ns to MHz

        step_results['timing_metrics'] = {
            'arrival_time': arrival_time,
            'slack': slack,
            'frequency': frequency
        }

        # Store execution metadata locally for debugging
        debug_log = f"{step_debug_dir}/execution_log.txt"
        with open(debug_log, 'w') as f:
            f.write(f"Step 05 - Timing Analysis with OpenSTA\n")
            f.write(f"Execution Time: {time.time() - start_time:.2f}s\n")
            f.write(f"Benchmark: {benchmark.get('name', 'Unknown')}\n")
            f.write(f"Top Module: {top_module}\n")
            f.write(f"Synth File: {synth_file}\n")
            f.write(f"Liberty File: {liberty_file}\n")
            f.write(f"SDC File: {sdc_file}\n")
            f.write(f"OpenSTA Return Code: {step_results['opensta_execution']['ret']}\n")
            f.write(f"Arrival Time: {arrival_time} ns\n")
            f.write(f"Slack: {slack} ns\n")
            f.write(f"Frequency: {frequency} MHz\n")

        # Store timing report locally for debugging
        if report_content:
            timing_report_local = f"{step_debug_dir}/timing_report.rpt"
            with open(timing_report_local, 'w') as f:
                f.write(report_content)

        # Store TCL script locally for debugging
        tcl_local = f"{step_debug_dir}/run_sta.tcl"
        with open(tcl_local, 'w') as f:
            f.write(tcl_content)

        # Update metrics in main data structure
        if 'metrics' not in data_copy:
            data_copy['metrics'] = {}

        data_copy['metrics']['original_arrival_time'] = arrival_time
        data_copy['metrics']['original_slack'] = slack
        data_copy['metrics']['original_frequency'] = frequency

        # Update file paths
        if 'file_paths' not in data_copy:
            data_copy['file_paths'] = {}
        data_copy['file_paths']['timing_report'] = timing_report_file
        data_copy['file_paths']['sta_tcl'] = sta_tcl_file

        # Store execution time and results
        step_results['execution_time'] = time.time() - start_time
        step_results['success'] = (ret == 0 and arrival_time is not None)

        if 'step_results' not in data_copy:
            data_copy['step_results'] = {}
        data_copy['step_results']['step_05_timing_analysis'] = step_results

        return data_copy


if __name__ == '__main__':
    timing_analysis_step = TimingAnalysis()
    timing_analysis_step.parse_arguments()
    timing_analysis_step.setup()
    timing_analysis_step.step()