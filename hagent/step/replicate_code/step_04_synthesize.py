#!/usr/bin/env python3
# See LICENSE for details

from typing import Dict
import time
import os

from hagent.step.replicate_code.schema import PipelineConfig
from hagent.step.replicate_code.opt_pipe_step_base import OptPipeStepBase


class Synthesize(OptPipeStepBase):
    """
    Example of what this function does: pipelinedCPU.v(rtl)---{yosys}--->nl_single/PipelinedCPU_synth.v (netlist)
    """
    def __init__(self):
        super().__init__()
        self.step_name = 'step_04_synthesize'

    def setup(self):
        super().setup()

    def run(self, data: Dict) -> Dict:
        # Parse input dictionary into typed configuration
        self.config = PipelineConfig.from_dict(data)

        self.prepare_environment(self.config, self.step_name)
        assert self.runner is not None

        # Access configuration via typed fields
        top_module_file = self.config.populated_file_paths.rtl_selected_top_file
        if not top_module_file:
            self.error('Top module file not populated from previous step results')

        top_module = self.config.benchmark.top_module
        liberty_file = self.config.tools.liberty_file
        yosys_cmd = self.config.tools.yosys_cmd

        if not top_module or not liberty_file:
            self.error('Missing required configuration: top_module, or liberty_file')

        # Create synthesis directory
        synth_dir = os.path.join(self.work_dir, 'nl_single')
        self._prepare_dir(synth_dir)

        # Define synthesis output file
        synth_file = f'{synth_dir}/{top_module}_synth.v'

        # Run Yosys synthesis
        yosys_script = f"""
            read_verilog -sv -defer {self.config.populated_file_paths.rtl_path}/*.sv;
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

        self.logger.info(f'Synthesizing original design with Yosys: {top_module}')
        ret, out, err = self.runner.run_cmd(f'{yosys_cmd} -p "{yosys_script}"', quiet=True)
        self.step_results['yosys_synthesis'] = {
            'ret': ret,
            'stdout': out,
            'stderr': err,
            'command': f'{yosys_cmd} -p "{yosys_script}"',
        }

        if ret != 0:
            self.logger.error('Yosys synthesis failed!')
            self.logger.error(f'Return code: {ret}')
            self.logger.error(f'STDOUT:\n{out}')
            self.logger.error(f'STDERR:\n{err}')
            self.error(f'Yosys synthesis failed: {err}')

        # Verify the synthesis file was created
        self.logger.info(f'Verifying synthesis output: {synth_file}')
        ret, out, err = self.runner.run_cmd(f'ls -la {synth_file}', quiet=True)
        self.step_results['file_verification'] = {'ret': ret, 'stdout': out, 'stderr': err}

        # Get synthesis statistics
        ret, out, err = self.runner.run_cmd(f'wc -l {synth_file}', quiet=True)
        self.step_results['file_stats'] = {'ret': ret, 'stdout': out, 'stderr': err}

        # Store execution metadata locally for debugging
        debug_log = f'{self.step_debug_dir}/execution_log.txt'
        self.logger.info(f'Writing debug log to {debug_log}')
        with open(debug_log, 'w') as f:
            f.write('Step 04 - Synthesize Original Design\n')
            f.write(f'Execution Time: {time.time() - self.start_time:.2f}s\n')
            f.write(f'Benchmark: {self.config.benchmark.name}\n')
            f.write(f'Top Module: {top_module}\n')
            f.write(f'Input File: {top_module_file}\n')
            f.write(f'Output File: {synth_file}\n')
            f.write(f'Liberty File: {liberty_file}\n')
            f.write(f'Yosys Return Code: {self.step_results["yosys_synthesis"]["ret"]}\n')
            if self.step_results['yosys_synthesis']['ret'] == 0:
                f.write('Synthesis Completed Successfully\n')
            else:
                f.write(f'Synthesis Error: {self.step_results["yosys_synthesis"]["stderr"]}\n')

        # Store synthesis log locally for debugging
        synth_log_file = f'{self.step_debug_dir}/synthesis_log.txt'
        self.logger.info(f'Writing synthesis log to {synth_log_file}')
        with open(synth_log_file, 'w') as f:
            f.write('Yosys Synthesis Output:\n')
            f.write('=====================\n')
            f.write(self.step_results['yosys_synthesis']['stdout'])
            if self.step_results['yosys_synthesis']['stderr']:
                f.write('\n\nYosys Synthesis Errors:\n')
                f.write('======================\n')
                f.write(self.step_results['yosys_synthesis']['stderr'])

        # Update populated file paths in config
        self.config.populated_file_paths.synth_dir = synth_dir
        self.config.populated_file_paths.synth_file = synth_file

        # Store execution time and results
        self.step_results['execution_time'] = time.time() - self.start_time
        self.step_results['success'] = ret == 0

        # Save step results to file and store reference in config
        results_file = self.save_step_results()
        self.config.step_results[self.step_name] = {'results_file': results_file}

        # Convert back to dict for pipeline compatibility
        return self.config.to_dict()


if __name__ == '__main__':
    synthesize_step = Synthesize()
    synthesize_step.parse_arguments()
    synthesize_step.setup()
    synthesize_step.step()
