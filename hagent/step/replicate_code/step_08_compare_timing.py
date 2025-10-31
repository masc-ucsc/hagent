#!/usr/bin/env python3
# See LICENSE for details

from hagent.inou.runner import Runner
from hagent.core.step import Step
from typing import Dict
import os
import time
import re


class CompareTiming(Step):
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
            self.error(f'OOPS in step_08_compare_timing.py error from runner:{self.runner.get_error()}')
            return data_copy

        # Create debug directory
        cache_dir = os.getenv('HAGENT_CACHE_DIR', local_storage.get('debug_base_dir', '/tmp/rtl_optimization_debug'))
        timestamp = str(int(time.time()))
        step_debug_dir = f"{cache_dir}/step08_compare_timing_{timestamp}"
        os.makedirs(step_debug_dir, exist_ok=True)

        step_results = {
            'start_time': start_time,
            'debug_directory': step_debug_dir,
            'timestamp': timestamp
        }

        # Get configuration
        top_module = benchmark.get('top_module')
        liberty_file = tools.get('liberty_file')
        yosys_cmd = tools.get('yosys_cmd', 'yosys')
        opensta_path = tools.get('opensta_path', '~/opensta/OpenSTA/app/sta')
        rtl_modules_dir = data_copy.get('file_paths', {}).get('rtl_modules_dir', '/tmp/rtl_modules')
        results_dir = data_copy.get('file_paths', {}).get('results_dir')
        optimization_results = data_copy.get('metrics', {}).get('modules_optimized', [])

        # Create optimized RTL directory
        optimized_rtl_dir = '/tmp/rtl_optimized'
        ret, out, err = self.runner.run(f'rm -rf {optimized_rtl_dir} && mkdir -p {optimized_rtl_dir}')

        # Copy original modules (excluding optimized ones)
        ret, out, err = self.runner.run(f'cp {rtl_modules_dir}/liveparse/*.v {optimized_rtl_dir}/')
        step_results['original_modules_copy'] = {
            'ret': ret, 'stdout': out, 'stderr': err
        }

        # Find and copy optimized modules
        optimized_files_found = []
        for opt_result in optimization_results:
            if not opt_result.get('success', False):
                continue

            module_name = opt_result['module_name']
            module_results_dir = f"{results_dir}/{module_name}"

            # Look for _optimized_*.v files in the module results directory
            ret, out, err = self.runner.run(f'find {module_results_dir} -name "*_optimized_*.v" | head -1')
            if ret == 0 and out.strip():
                optimized_file = out.strip()
                target_file = f"{optimized_rtl_dir}/{module_name}.v"

                # Copy optimized module, replacing original
                ret, out, err = self.runner.run(f'cp {optimized_file} {target_file}')
                if ret == 0:
                    optimized_files_found.append({
                        'module_name': module_name,
                        'optimized_file': optimized_file,
                        'target_file': target_file
                    })

        step_results['optimized_modules'] = {
            'files_found': len(optimized_files_found),
            'modules': optimized_files_found
        }

        # Synthesize optimized design
        optimized_synth_dir = '/tmp/nl_optimized'
        ret, out, err = self.runner.run(f'rm -rf {optimized_synth_dir} && mkdir -p {optimized_synth_dir}')

        optimized_synth_file = f"{optimized_synth_dir}/{top_module}_optimized_synth.v"

        yosys_script = f"""
            read_verilog -sv -defer {optimized_rtl_dir}/*.v;
            hierarchy -top {top_module};
            flatten {top_module};
            opt;
            synth -top {top_module};
            dfflibmap -liberty {liberty_file};
            printattrs;
            stat;
            abc -liberty {liberty_file} -dff -keepff -g aig;
            stat;
            write_verilog {optimized_synth_file};
        """

        ret, out, err = self.runner.run(f'{yosys_cmd} -p "{yosys_script}"')
        step_results['optimized_synthesis'] = {
            'ret': ret, 'stdout': out, 'stderr': err,
            'command': f'{yosys_cmd} -p "{yosys_script}"'
        }

        if ret != 0:
            self.error(f"Optimized synthesis failed: {err}")
            return data_copy

        # Run timing analysis on optimized design
        optimized_timing_report = "/tmp/timing_report_optimized.rpt"
        sdc_file = data_copy.get('file_paths', {}).get('sdc_file', f"/tmp/{top_module}.sdc")

        tcl_content = f"""
read_liberty {liberty_file}
set_units -time ns -capacitance pF -voltage V -current mA -resistance kOhm -distance um
set_operating_conditions ff_100C_1v95
read_verilog {optimized_synth_file}
link_design {top_module}
read_sdc {sdc_file}
report_checks -path_delay max > {optimized_timing_report}
"""

        optimized_sta_tcl = "/tmp/run_sta_optimized.tcl"
        ret, out, err = self.runner.run(f'cat > {optimized_sta_tcl} << "EOF"\n{tcl_content}\nEOF')

        ret, out, err = self.runner.run(f'echo "source {optimized_sta_tcl}" | {opensta_path}')
        step_results['optimized_timing_analysis'] = {
            'ret': ret, 'stdout': out, 'stderr': err
        }

        # Parse optimized timing results
        ret, report_content, err = self.runner.run(f'cat {optimized_timing_report}')
        optimized_arrival_time = None
        optimized_slack = None
        optimized_frequency = None

        if report_content:
            arrival_match = re.search(r'(\d+\.\d+)\s+data arrival time', report_content)
            if arrival_match:
                optimized_arrival_time = float(arrival_match.group(1))

            slack_match = re.search(r'(-?\d+\.\d+)\s+slack', report_content)
            if slack_match:
                optimized_slack = float(slack_match.group(1))

            if optimized_arrival_time and optimized_arrival_time > 0:
                optimized_frequency = 1000.0 / optimized_arrival_time

        # Calculate improvements
        original_arrival_time = data_copy.get('metrics', {}).get('original_arrival_time')
        original_slack = data_copy.get('metrics', {}).get('original_slack')
        original_frequency = data_copy.get('metrics', {}).get('original_frequency')

        arrival_time_improvement = None
        slack_improvement = None
        frequency_improvement = None

        if original_arrival_time and optimized_arrival_time:
            arrival_time_improvement = original_arrival_time - optimized_arrival_time

        if original_slack and optimized_slack:
            slack_improvement = optimized_slack - original_slack

        if original_frequency and optimized_frequency:
            frequency_improvement = optimized_frequency - original_frequency

        # Store execution metadata locally for debugging
        debug_log = f"{step_debug_dir}/execution_log.txt"
        with open(debug_log, 'w') as f:
            f.write(f"Step 08 - Compare Timing (Optimized vs Original)\n")
            f.write(f"Execution Time: {time.time() - start_time:.2f}s\n")
            f.write(f"Benchmark: {benchmark.get('name', 'Unknown')}\n")
            f.write(f"Optimized Modules Found: {len(optimized_files_found)}\n\n")

            f.write(f"ORIGINAL TIMING:\n")
            f.write(f"  Arrival Time: {original_arrival_time} ns\n")
            f.write(f"  Slack: {original_slack} ns\n")
            f.write(f"  Frequency: {original_frequency} MHz\n\n")

            f.write(f"OPTIMIZED TIMING:\n")
            f.write(f"  Arrival Time: {optimized_arrival_time} ns\n")
            f.write(f"  Slack: {optimized_slack} ns\n")
            f.write(f"  Frequency: {optimized_frequency} MHz\n\n")

            f.write(f"IMPROVEMENTS:\n")
            f.write(f"  Arrival Time: {arrival_time_improvement} ns\n")
            f.write(f"  Slack: {slack_improvement} ns\n")
            f.write(f"  Frequency: {frequency_improvement} MHz\n\n")

            f.write(f"OPTIMIZATION SUMMARY:\n")
            for result in optimization_results:
                f.write(f"  {result['module_name']}: {'SUCCESS' if result['success'] else 'FAILED'} "
                       f"({result['tokens_used']} tokens, {result['execution_time']:.2f}s)\n")

        # Store timing reports locally
        if report_content:
            with open(f"{step_debug_dir}/timing_report_optimized.rpt", 'w') as f:
                f.write(report_content)

        # Update final metrics
        if 'metrics' not in data_copy:
            data_copy['metrics'] = {}

        data_copy['metrics']['optimized_arrival_time'] = optimized_arrival_time
        data_copy['metrics']['optimized_slack'] = optimized_slack
        data_copy['metrics']['optimized_frequency'] = optimized_frequency
        data_copy['metrics']['arrival_time_improvement'] = arrival_time_improvement
        data_copy['metrics']['slack_improvement'] = slack_improvement
        data_copy['metrics']['frequency_improvement'] = frequency_improvement
        data_copy['metrics']['end_time'] = time.time()
        data_copy['metrics']['total_execution_time'] = time.time() - data_copy['metrics'].get('start_time', start_time)

        step_results['timing_comparison'] = {
            'original': {
                'arrival_time': original_arrival_time,
                'slack': original_slack,
                'frequency': original_frequency
            },
            'optimized': {
                'arrival_time': optimized_arrival_time,
                'slack': optimized_slack,
                'frequency': optimized_frequency
            },
            'improvements': {
                'arrival_time': arrival_time_improvement,
                'slack': slack_improvement,
                'frequency': frequency_improvement
            }
        }

        # Store execution time and results
        step_results['execution_time'] = time.time() - start_time
        step_results['success'] = (optimized_arrival_time is not None)

        if 'step_results' not in data_copy:
            data_copy['step_results'] = {}
        data_copy['step_results']['step_08_compare_timing'] = step_results

        return data_copy


if __name__ == '__main__':
    compare_timing_step = CompareTiming()
    compare_timing_step.parse_arguments()
    compare_timing_step.setup()
    compare_timing_step.step()