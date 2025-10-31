#!/usr/bin/env python3
# See LICENSE for details

from hagent.inou.runner import Runner
from hagent.core.step import Step
from typing import Dict
import os
import time


class Synthesize(Step):
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
            self.error(f'OOPS in step_04_synthesize.py error from runner:{self.runner.get_error()}')
            return data_copy

        # Create debug directory
        cache_dir = os.getenv('HAGENT_CACHE_DIR', local_storage.get('debug_base_dir', '/tmp/rtl_optimization_debug'))
        timestamp = str(int(time.time()))
        step_debug_dir = f"{cache_dir}/step04_synthesize_{timestamp}"
        os.makedirs(step_debug_dir, exist_ok=True)

        step_results = {
            'start_time': start_time,
            'debug_directory': step_debug_dir,
            'timestamp': timestamp
        }

        # Get configuration
        top_module_file = data_copy.get('file_paths', {}).get('top_module_file')
        top_module = benchmark.get('top_module')
        liberty_file = tools.get('liberty_file')
        yosys_cmd = tools.get('yosys_cmd', 'yosys')

        if not top_module_file or not top_module or not liberty_file:
            self.error("Missing required configuration: top_module_file, top_module, or liberty_file")
            return data_copy

        # Create synthesis directory
        synth_dir = '/tmp/nl_single'
        ret, out, err = self.runner.run(f'rm -rf {synth_dir} && mkdir -p {synth_dir}')
        step_results['directory_setup'] = {
            'ret': ret, 'stdout': out, 'stderr': err
        }

        # Define synthesis output file
        synth_file = f"{synth_dir}/{top_module}_synth.v"

        # Create SDC file for timing constraints
        sdc_file = f"/tmp/{top_module}.sdc"
        sdc_content = f"""
# Basic SDC constraints for {top_module}
set_operating_conditions ff_100C_1v95
create_clock -name clk -period 10.0 [get_ports clk]
set_input_delay 1.0 [all_inputs]
set_output_delay 1.0 [all_outputs]
set_load 0.1 [all_outputs]
"""
        ret, out, err = self.runner.run(f'cat > {sdc_file} << "EOF"\n{sdc_content}\nEOF')
        step_results['sdc_creation'] = {
            'ret': ret, 'stdout': out, 'stderr': err
        }

        # Run Yosys synthesis
        yosys_script = f"""
            read_verilog -sv -defer {top_module_file};
            hierarchy -top {top_module};
            flatten {top_module};
            opt;
            synth -top {top_module};
            dfflibmap -liberty {liberty_file};
            printattrs;
            stat;
            abc -liberty {liberty_file} -dff -keepff -g aig;
            stat;
            write_verilog {synth_file};
        """

        ret, out, err = self.runner.run(f'{yosys_cmd} -p "{yosys_script}"')
        step_results['yosys_synthesis'] = {
            'ret': ret, 'stdout': out, 'stderr': err,
            'command': f'{yosys_cmd} -p "{yosys_script}"'
        }

        if ret != 0:
            self.error(f"Yosys synthesis failed: {err}")
            return data_copy

        # Verify the synthesis file was created
        ret, out, err = self.runner.run(f'ls -la {synth_file}')
        step_results['file_verification'] = {
            'ret': ret, 'stdout': out, 'stderr': err
        }

        # Get synthesis statistics
        ret, out, err = self.runner.run(f'wc -l {synth_file}')
        step_results['file_stats'] = {
            'ret': ret, 'stdout': out, 'stderr': err
        }

        # Store execution metadata locally for debugging
        debug_log = f"{step_debug_dir}/execution_log.txt"
        with open(debug_log, 'w') as f:
            f.write(f"Step 04 - Synthesize Original Design\n")
            f.write(f"Execution Time: {time.time() - start_time:.2f}s\n")
            f.write(f"Benchmark: {benchmark.get('name', 'Unknown')}\n")
            f.write(f"Top Module: {top_module}\n")
            f.write(f"Input File: {top_module_file}\n")
            f.write(f"Output File: {synth_file}\n")
            f.write(f"Liberty File: {liberty_file}\n")
            f.write(f"SDC File: {sdc_file}\n")
            f.write(f"Yosys Return Code: {step_results['yosys_synthesis']['ret']}\n")
            if step_results['yosys_synthesis']['ret'] == 0:
                f.write(f"Synthesis Completed Successfully\n")
            else:
                f.write(f"Synthesis Error: {step_results['yosys_synthesis']['stderr']}\n")

        # Store synthesis log locally for debugging
        synth_log_file = f"{step_debug_dir}/synthesis_log.txt"
        with open(synth_log_file, 'w') as f:
            f.write("Yosys Synthesis Output:\n")
            f.write("=====================\n")
            f.write(step_results['yosys_synthesis']['stdout'])
            if step_results['yosys_synthesis']['stderr']:
                f.write("\n\nYosys Synthesis Errors:\n")
                f.write("======================\n")
                f.write(step_results['yosys_synthesis']['stderr'])

        # Update file paths
        if 'file_paths' not in data_copy:
            data_copy['file_paths'] = {}
        data_copy['file_paths']['synth_dir'] = synth_dir
        data_copy['file_paths']['synth_file'] = synth_file
        data_copy['file_paths']['sdc_file'] = sdc_file

        # Store execution time and results
        step_results['execution_time'] = time.time() - start_time
        step_results['success'] = (ret == 0)

        if 'step_results' not in data_copy:
            data_copy['step_results'] = {}
        data_copy['step_results']['step_04_synthesize'] = step_results

        return data_copy


if __name__ == '__main__':
    synthesize_step = Synthesize()
    synthesize_step.parse_arguments()
    synthesize_step.setup()
    synthesize_step.step()