#!/usr/bin/env python3
# See LICENSE for details

from typing import Dict
import time
import re
import os

from hagent.step.replicate_code.schema import PipelineConfig
from hagent.step.replicate_code.opt_pipe_step_base import OptPipeStepBase


class CompareTiming(OptPipeStepBase):
    def __init__(self):
        super().__init__()
        self.step_name = 'step_08_compare_timing'

    def setup(self):
        super().setup()

    def run(self, data: Dict) -> Dict:
        # Parse input dictionary into typed configuration
        self.config = PipelineConfig.from_dict(data)

        self.prepare_environment(self.config, self.step_name)
        assert self.runner is not None

        # Access configuration via typed fields
        top_module = self.config.benchmark.top_module
        liberty_file = self.config.tools.liberty_file
        yosys_cmd = self.config.tools.yosys_cmd
        opensta_path = self.config.tools.opensta_path
        rtl_modules_dir = self.config.populated_file_paths.rtl_path
        optimization_results = self.config.metrics.modules_optimized

        self.logger.info('Preparing optimized design for timing comparison')

        # Get rtl_optimized directory from step_07
        rtl_optimized_dir = self.config.populated_file_paths.optimized_dir
        if not rtl_optimized_dir or not os.path.exists(rtl_optimized_dir):
            self.error('Previous step did not produce rtl_optimized directory')

        # Create directory for synthesis (contains original + optimized modules)
        optimized_rtl_dir = os.path.join(self.work_dir, "rtl_for_synthesis")
        self._prepare_dir(optimized_rtl_dir)

        # Copy ALL original modules first
        self.logger.info('Copying original module files')
        ret, out, err = self.runner.run_cmd(f'cp {rtl_modules_dir}/liveparse/*.v {optimized_rtl_dir}/', quiet=True)
        self.step_results['original_modules_copy'] = {'ret': ret, 'stdout': out, 'stderr': err}
        if ret != 0:
            self.error(f'Failed to copy original modules: {err}')

        # Copy best optimized variants from step_07 (overwrite originals)
        self.logger.info(f'Copying best optimized variants from {rtl_optimized_dir}')
        ret, out, err = self.runner.run_cmd(f'cp {rtl_optimized_dir}/*.v {optimized_rtl_dir}/', quiet=True)
        self.step_results['optimized_modules_copy'] = {'ret': ret, 'stdout': out, 'stderr': err}

        # Track which modules were optimized
        optimized_files_found = []
        for opt_result in optimization_results:
            if opt_result.success and opt_result.best_variant_file:
                module_name = opt_result.module_name
                optimized_files_found.append({
                    'module_name': module_name,
                    'best_variant_file': opt_result.best_variant_file,
                    'best_variant_timing': opt_result.best_variant_timing,
                    'num_variants': opt_result.num_variants,
                })

        self.step_results['optimized_modules'] = {
            'count': len(optimized_files_found),
            'modules': optimized_files_found
        }

        self.logger.info(f'Integrated {len(optimized_files_found)} optimized modules with original design')

        # Synthesize optimized design
        self.logger.info('Synthesizing optimized design')

        optimized_synth_dir = os.path.join(self.work_dir, 'nl_optimized')
        self._prepare_dir(optimized_synth_dir)

        optimized_synth_file = f'{optimized_synth_dir}/{top_module}_optimized_synth.v'

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

        ret, out, err = self.runner.run_cmd(f'{yosys_cmd} -p "{yosys_script}"')
        self.step_results['optimized_synthesis'] = {
            'ret': ret,
            'stdout': out,
            'stderr': err,
            'command': f'{yosys_cmd} -p "{yosys_script}"',
        }

        if ret != 0:
            self.error(f'Optimized synthesis failed: {err}')

        # Run timing analysis on optimized design
        optimized_timing_report = os.path.join(self.work_dir, 'timing_report_optimized.rpt')
        sdc_file = self.config.tools.sdc_file

        tcl_content = f"""
read_liberty {liberty_file}
set_units -time ns -capacitance pF -voltage V -current mA -resistance kOhm -distance um
set_operating_conditions ff_100C_1v95
read_verilog {optimized_synth_file}
link_design {top_module}
read_sdc {sdc_file}
report_checks -path_delay max > {optimized_timing_report}
exit
"""

        optimized_sta_tcl = os.path.join(self.work_dir, 'run_sta_optimized.tcl')
        ret, out, err = self.runner.run_cmd(f'cat > {optimized_sta_tcl} << "EOF"\n{tcl_content}\nEOF')

        ret, out, err = self.runner.run_cmd(f'echo "source {optimized_sta_tcl}" | {opensta_path}')
        self.step_results['optimized_timing_analysis'] = {'ret': ret, 'stdout': out, 'stderr': err}

        # Parse optimized timing results
        ret, report_content, err = self.runner.run_cmd(f'cat {optimized_timing_report}')
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
        original_slack = self.config.metrics.original_slack
        original_frequency = self.config.metrics.original_frequency

        # Get original arrival time from step_05 results
        original_arrival_time = None
        if 'step_05_timing_analysis' in self.config.step_results:
            step_05_results = self.load_step_results_from_path(
                self.config.step_results['step_05_timing_analysis']['results_file']
            )
            timing_metrics = step_05_results.get('timing_metrics', {})
            original_arrival_time = timing_metrics.get('arrival_time')

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
        debug_log = f'{self.step_debug_dir}/execution_log.txt'
        with open(debug_log, 'w') as f:
            f.write('Step 08 - Compare Timing (Optimized vs Original)\n')
            f.write(f'Execution Time: {time.time() - self.start_time:.2f}s\n')
            f.write(f'Benchmark: {self.config.benchmark.name}\n')
            f.write(f'Optimized Modules Found: {len(optimized_files_found)}\n\n')

            f.write('ORIGINAL TIMING:\n')
            f.write(f'  Arrival Time: {original_arrival_time} ns\n')
            f.write(f'  Slack: {original_slack} ns\n')
            f.write(f'  Frequency: {original_frequency} MHz\n\n')

            f.write('OPTIMIZED TIMING:\n')
            f.write(f'  Arrival Time: {optimized_arrival_time} ns\n')
            f.write(f'  Slack: {optimized_slack} ns\n')
            f.write(f'  Frequency: {optimized_frequency} MHz\n\n')

            f.write('IMPROVEMENTS:\n')
            f.write(f'  Arrival Time: {arrival_time_improvement} ns\n')
            f.write(f'  Slack: {slack_improvement} ns\n')
            f.write(f'  Frequency: {frequency_improvement} MHz\n\n')

            f.write('OPTIMIZATION SUMMARY:\n')
            for result in optimization_results:
                status = "SUCCESS" if result.success else "FAILED"
                f.write(f'  {result.module_name}: {status}\n')
                if result.success:
                    f.write(f'    Variants: {getattr(result, "num_variants", "N/A")}\n')
                    if result.best_variant_timing:
                        f.write(f'    Best Variant Timing: {result.best_variant_timing:.2f} ns\n')
                f.write(f'    Tokens: {result.tokens_used}, Time: {result.execution_time:.2f}s\n')

        # Store timing reports locally
        if report_content:
            with open(f'{self.step_debug_dir}/timing_report_optimized.rpt', 'w') as f:
                f.write(report_content)

        # Update populated file paths
        self.config.populated_file_paths.optimized_dir = optimized_rtl_dir

        # Update final metrics
        self.config.metrics.end_time = time.time()
        if self.config.metrics.start_time:
            self.config.metrics.total_execution_time = self.config.metrics.end_time - self.config.metrics.start_time

        self.step_results['timing_comparison'] = {
            'original': {'arrival_time': original_arrival_time, 'slack': original_slack, 'frequency': original_frequency},
            'optimized': {'arrival_time': optimized_arrival_time, 'slack': optimized_slack, 'frequency': optimized_frequency},
            'improvements': {
                'arrival_time': arrival_time_improvement,
                'slack': slack_improvement,
                'frequency': frequency_improvement,
            },
        }

        # Store execution time and results
        self.step_results['execution_time'] = time.time() - self.start_time
        self.step_results['success'] = optimized_arrival_time is not None

        # Save step results to file and store reference in config
        results_file = self.save_step_results()
        self.config.step_results[self.step_name] = {'results_file': results_file}

        # Convert back to dict for pipeline compatibility
        return self.config.to_dict()


if __name__ == '__main__':
    compare_timing_step = CompareTiming()
    compare_timing_step.parse_arguments()
    compare_timing_step.setup()
    compare_timing_step.step()
