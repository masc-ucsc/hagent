#!/usr/bin/env python3
# See LICENSE for details

from typing import Dict
import time
import re
import os

from hagent.step.replicate_code.schema import PipelineConfig
from hagent.step.replicate_code.opt_pipe_step_base import OptPipeStepBase


class TimingAnalysis(OptPipeStepBase):
    """
    TODO: need to create color.json when running with SynAlign
    Example of what this function does: nl_single/PipelinedCPU_synth.v (netlist) --openSTA---> timing_report*rpt formed with max delay path -----> color.json
    """
    def __init__(self):
        super().__init__()
        self.step_name = 'step_05_timing_analysis'

    def setup(self):
        super().setup()

    def _run_impl(self, data: Dict):
        # Parse input dictionary into typed configuration
        config = PipelineConfig.from_dict(data)

        self.prepare_environment(config, self.step_name)
        assert self.runner is not None

        # Access configuration via typed fields
        synth_file = config.populated_file_paths.synth_file
        if not synth_file:
            self.error('Synthesis netlist file not populated from previous step results')

        top_module = config.benchmark.top_module
        sdc_file = config.tools.sdc_file

        liberty_file = config.tools.liberty_file
        opensta_path = config.tools.opensta_path

        if not top_module or not liberty_file or not opensta_path:
            self.error('Missing required configuration: top_module, liberty_file, or opensta_path')

        # Create TCL script for OpenSTA
        sta_tcl_file = os.path.join(self.work_dir, 'run_sta.tcl')
        timing_report_file = os.path.join(self.work_dir, 'timing_report.rpt')

        tcl_content = f"""
read_liberty {liberty_file}
set_units -time ns -capacitance pF -voltage V -current mA -resistance kOhm -distance um
set_operating_conditions ff_100C_1v95
read_verilog {synth_file}
link_design {top_module}
read_sdc {sdc_file}
report_checks -path_delay max > {timing_report_file}
"""

        self.logger.info('Creating OpenSTA TCL script')
        ret, out, err = self.runner.run_cmd(f'cat > {sta_tcl_file} << "EOF"\n{tcl_content}\nEOF', quiet=True)
        self.step_results['tcl_creation'] = {'ret': ret, 'stdout': out, 'stderr': err}

        # Run OpenSTA
        self.logger.info('Running timing analysis with OpenSTA')
        ret, out, err = self.runner.run_cmd(f'echo "source {sta_tcl_file}" | {opensta_path}', quiet=True)
        self.step_results['opensta_execution'] = {
            'ret': ret,
            'stdout': out,
            'stderr': err,
            'command': f'echo "source {sta_tcl_file}" | {opensta_path}',
        }

        # Read timing report
        ret, report_content, err = self.runner.run_cmd(f'cat {timing_report_file}', quiet=True)
        self.step_results['timing_report'] = {'ret': ret, 'content': report_content, 'stderr': err}

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

        self.step_results['timing_metrics'] = {'arrival_time': arrival_time, 'slack': slack, 'frequency': frequency}

        self.logger.info(f'Timing analysis complete: slack={slack}ns, frequency={frequency}MHz')

        # Store execution metadata locally for debugging
        debug_log = f'{self.step_debug_dir}/execution_log.txt'
        self.logger.info(f'Writing debug log to {debug_log}')
        with open(debug_log, 'w') as f:
            f.write('Step 05 - Timing Analysis with OpenSTA\n')
            f.write(f'Execution Time: {time.time() - self.start_time:.2f}s\n')
            f.write(f'Benchmark: {config.benchmark.name}\n')
            f.write(f'Top Module: {top_module}\n')
            f.write(f'Synth File: {synth_file}\n')
            f.write(f'Liberty File: {liberty_file}\n')
            f.write(f'SDC File: {sdc_file}\n')
            f.write(f'OpenSTA Return Code: {self.step_results["opensta_execution"]["ret"]}\n')
            f.write(f'Arrival Time: {arrival_time} ns\n')
            f.write(f'Slack: {slack} ns\n')
            f.write(f'Frequency: {frequency} MHz\n')

        # Store timing report and TCL script locally for debugging
        if report_content:
            timing_report_local = f'{self.step_debug_dir}/timing_report.rpt'
            with open(timing_report_local, 'w') as f:
                f.write(report_content)

        tcl_local = f'{self.step_debug_dir}/run_sta.tcl'
        with open(tcl_local, 'w') as f:
            f.write(tcl_content)

        # Update metrics in config
        config.metrics.original_slack = slack
        config.metrics.original_frequency = frequency

        # Store execution time and results
        self.step_results['execution_time'] = time.time() - self.start_time
        self.step_results['success'] = ret == 0 and arrival_time is not None

        # Save step results to file and store reference in config
        results_file = self.save_step_results()
        config.step_results[self.step_name] = {'results_file': results_file}

        # Convert back to dict for pipeline compatibility
        return config.to_dict()


if __name__ == '__main__':
    timing_analysis_step = TimingAnalysis()
    timing_analysis_step.parse_arguments()
    timing_analysis_step.setup()
    timing_analysis_step.step()
