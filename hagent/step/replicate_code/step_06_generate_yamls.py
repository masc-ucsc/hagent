#!/usr/bin/env python3
# See LICENSE for details

from typing import Dict, List, Optional
from pathlib import Path
import os
import time
import yaml
import re
import subprocess
import sys

from hagent.step.replicate_code.schema import PipelineConfig
from hagent.step.replicate_code.opt_pipe_step_base import OptPipeStepBase


class GenerateYamls(OptPipeStepBase):
    """Read the timing report and gather the related Verilog modules from the target RTL directory and create YAML configuration files for each module as HAgent input."""

    def __init__(self):
        super().__init__()
        self.step_name = 'step_06_generate_yamls'

    def setup(self):
        super().setup()

    def run(self, data: Dict) -> Dict:
        # Parse input dictionary into typed configuration
        self.config = PipelineConfig.from_dict(data)

        self.prepare_environment(self.config, self.step_name)
        assert self.runner is not None

        # Create directories locally (outside docker)
        modules_to_optimize_dir = os.path.join(self.work_dir, 'modules_to_optimize')
        self._prepare_dir(modules_to_optimize_dir)

        # Find .v files from liveparse directory
        rtl_modules_dir = self.config.populated_file_paths.rtl_path
        self.logger.info(f'Finding module files in {rtl_modules_dir}/liveparse')
        ret, out, err = self.runner.run_cmd(f'find {rtl_modules_dir}/liveparse -name "*.v" -type f | sort', quiet=True)
        if ret != 0:
            self.logger.error('Failed to find module files!')
            self.logger.error(f'STDOUT:\n{out}')
            self.logger.error(f'STDERR:\n{err}')
            self.error(f'Failed to find module files in {rtl_modules_dir}/liveparse: {err}')

        critical_path_modules = self._locate_module_names_with_timing_rpt(self.config.populated_file_paths.timing_report_file)
        module_files = [f.strip() for f in out.split('\n') if f.strip()] if out else []
        self.step_results['module_discovery'] = {'ret': ret, 'stdout': out, 'stderr': err, 'module_files': module_files}
        self.step_results['critical_path_modules'] = critical_path_modules

        model = self.config.optimization.model
        run_with_synalign = self.config.optimization.run_with_synalign

        generated_yamls = []
        modules_processed = []

        # Process each module file splitted in step 3
        critical_path_module_files = [path for path in module_files if any(mod in path for mod in critical_path_modules)]

        for module_file in critical_path_module_files:
            if not module_file:
                continue

            # Extract module name
            module_name = os.path.basename(module_file).replace('.v', '')

            # Read module content. The added `echo` ensures a trailing newline so that output from subsequent commands does not appear on the same line.
            ret, module_content, err = self.runner.run_cmd(f'cat {module_file}; echo', quiet=True)
            if ret != 0:
                continue

            if not module_content.endswith('\n'):
                module_content += '\n'

            # Create YAML content using the same structure as create_yaml_for_hagent.py
            yaml_content = {
                'replicate_code_prompt1': [
                    {
                        'role': 'system',
                        'content': (
                            'You are a super smart Verilog and timing expert. '
                            'You have been tasked with improving the frequency of a verilog code. '
                            'You provide a higher frequency code which passes LEC. '
                            'Make sure that you only return the code that passes LEC. '
                            'Take care that: '
                            'The semantics are preserved exactly as in the original netlist (including word instantiation and sign‐extension) '
                            'while breaking a long combinational critical path. '
                            'The resultant code is functionally equivalent to the original and passes LEC.'
                        ),
                    },
                    {
                        'role': 'user',
                        'content': (
                            'This is the current Verilog:\n```\n{code_content}\n```\n'
                            'Please do not change semantics, just split the always blocks in separate always blocks '
                            'and try to improve the performance when possible.'
                        ),
                    },
                ],
                'top_name': module_name,
                'llm': {'model': model},
                'code_content': module_content,
            }

            # Add threshold for o3 models
            if 'o3' in model:
                yaml_content['threshold'] = self.config.optimization.threshold
            elif 'o4' in model:
                yaml_content['temperature'] = self.config.optimization.threshold

            # Save YAML file locally
            yaml_filename = f'{module_name}.yaml'
            local_yaml_path = f'{modules_to_optimize_dir}/{yaml_filename}'

            with open(local_yaml_path, 'w') as f:
                yaml.dump(yaml_content, f, default_flow_style=False, sort_keys=False, allow_unicode=True, indent=2)

            generated_yamls.append(local_yaml_path)
            modules_processed.append({'module_name': module_name, 'source_file': module_file, 'yaml_file': local_yaml_path})

        self.step_results['yaml_generation'] = {
            'modules_processed': len(modules_processed),
            'yamls_generated': generated_yamls,
            'modules_info': modules_processed,
        }

        # Populate config for subsequent steps to use
        self.config.populated_file_paths.generated_input_yamls = generated_yamls

        self.logger.info(f'Generated {len(generated_yamls)} YAML files for optimization')

        # Store execution metadata locally for debugging
        debug_log = f'{self.step_debug_dir}/execution_log.txt'
        self.logger.info(f'Writing debug log to {debug_log}')
        with open(debug_log, 'w') as f:
            f.write('Step 06 - Generate YAML Files for Optimization\n')
            f.write(f'Execution Time: {time.time() - self.start_time:.2f}s\n')
            f.write(f'Benchmark: {self.config.benchmark.name}\n')
            f.write(f'Model: {model}\n')
            f.write(f'Run with SynAlign: {run_with_synalign}\n')
            f.write(f'Modules to Optimize Directory: {modules_to_optimize_dir}\n')
            f.write(f'Modules Processed: {len(modules_processed)}\n')
            f.write(f'Number of YAML Files Generated: {len(generated_yamls)}\n')
            for i, module_info in enumerate(modules_processed):
                f.write(f'  {i + 1}. {module_info["module_name"]}: {module_info["yaml_file"]}\n')

        # Store execution time and results
        self.step_results['execution_time'] = time.time() - self.start_time
        self.step_results['success'] = len(generated_yamls) > 0

        # Save step results to file and store reference in config
        results_file = self.save_step_results()
        self.config.step_results[self.step_name] = {'results_file': results_file}

        # Convert back to dict for pipeline compatibility
        return self.config.to_dict()

    def _invoke_locator(self, vcd_signal_path: str) -> List[tuple[str, int]]:
        """
        Invoke cli_locator.py to find the netlist location of a VCD signal.

        Args:
            vcd_signal_path: Full VCD hierarchical path (e.g., "PipelinedCPU.mem_wb_ctrl.reg_wb_ctrl_toreg")

        Returns:
            List of (file_path, line_number) tuples where the signal is found
        """
        # Build cli_locator.py command
        cli_locator_path = self.hagent_root_dir / 'hagent' / 'inou' / 'cli_locator.py'

        cmd = [
            sys.executable,
            str(cli_locator_path),
            '--config',
            self.config.benchmark.hagent_config_path,
            '--api',
            'locate_vcd',
            '--to',
            'verilog',
            '--top',
            self.config.benchmark.profile_name,
            vcd_signal_path,
        ]

        self.logger.debug(f'Invoking cli_locator: {" ".join(cmd)}')

        try:
            result = subprocess.run(cmd, capture_output=True, text=True, check=False)

            if result.returncode != 0:
                self.logger.warning(f'cli_locator failed for {vcd_signal_path}: {result.stderr}')
                return []

            # Parse output: format is "file_path:line_start-line_end"
            locations = []
            for line in result.stdout.strip().split('\n'):
                if not line:
                    continue
                # Parse "file_path:line_start-line_end"
                match = re.match(r'^(.+):(\d+)-(\d+)$', line)
                if match:
                    file_path = match.group(1)
                    line_start = int(match.group(2))
                    locations.append((file_path, line_start))

            self.logger.debug(f'Found {len(locations)} location(s) for {vcd_signal_path}')
            return locations

        except Exception as e:
            self.logger.error(f'Error invoking cli_locator for {vcd_signal_path}: {e}')
            return []

    def _extract_source_module_from_netlist(self, file_path: str, line_num: int) -> Optional[str]:
        """
        Extract the source module name from netlist annotations near a given line.

        Looks for (* src = "build_xxx/ModuleName.sv:line" *) annotations and extracts "ModuleName".

        Args:
            file_path: Path to the netlist file
            line_num: Line number where the signal is found

        Returns:
            Source module name (e.g., "StageReg_6") or None if not found
        """
        try:
            with open(file_path, 'r') as f:
                lines = f.readlines()

            # Search a few lines around the target line for (* src = "..." *) annotation
            search_start = max(0, line_num - 5)
            search_end = min(len(lines), line_num + 2)

            # Pattern: (* src = "build_xxx/ModuleName.sv:line.col" *)
            src_pattern = re.compile(r'\(\*\s*src\s*=\s*"[^/]+/([^/.]+)\.sv:\d+\.\d+"\s*\*\)')

            for i in range(search_start, search_end):
                match = src_pattern.search(lines[i])
                if match:
                    module_name = match.group(1)
                    self.logger.debug(f'Extracted source module "{module_name}" from {file_path}:{i + 1}')
                    return module_name

            self.logger.warning(f'No source module annotation found near {file_path}:{line_num}')
            return None

        except Exception as e:
            self.logger.error(f'Error reading netlist file {file_path}: {e}')
            return None

    def _locate_module_names_with_timing_rpt(self, timing_report: str | Path) -> List[str]:
        """
        Get the source module names that constitute the critical path.

        This method:
        1. Parses timing report to extract launch/capture flip-flop instances
        2. Extracts Q signal names from the netlist
        3. Invokes cli_locator to find VCD signal locations in the netlist
        4. Extracts source module names from netlist annotations

        Returns:
            List of source module names (e.g., ["StageReg_6", "StageReg_7"])
        """
        # Read the timing report to get critical path's starting Q and ending D
        with open(timing_report, 'r') as file:
            timing_text = file.read()
        launch_capture_pattern = re.compile(r'(_\d+_)/(Q|D)\s*\((.*?)\)')
        launch_capture_instances = launch_capture_pattern.findall(timing_text)
        launch = None
        capture = None
        for inst, pin, cell in launch_capture_instances:
            if pin == 'Q':
                assert launch is None
                launch = (inst, cell)
            if pin == 'D':
                assert capture is None
                capture = (inst, cell)
        assert launch is not None and capture is not None

        with open(self.config.populated_file_paths.synth_file, 'r') as f:
            verilog_text = f.read()

        launch_q_signal = self._extract_q_signal(verilog_text, launch[0])
        capture_q_signal = self._extract_q_signal(verilog_text, capture[0])

        self.logger.info(f'Launch Q signal: {launch_q_signal}')
        self.logger.info(f'Capture Q signal: {capture_q_signal}')

        # Construct full VCD hierarchical paths and find source modules
        source_modules = []
        top_module = self.config.benchmark.top_module

        for signal_name in [launch_q_signal, capture_q_signal]:
            # Construct full hierarchical VCD path: TopModule.signal.name
            vcd_path = f'{top_module}.{signal_name}'
            self.logger.debug(f'Looking up VCD path: {vcd_path}')

            # Invoke cli_locator to find netlist locations
            locations = self._invoke_locator(vcd_path)

            if not locations:
                self.logger.warning(f'No locations found for {vcd_path}')
                continue

            # Extract source module from first location
            file_path, line_num = locations[0]
            source_module = self._extract_source_module_from_netlist(file_path, line_num)

            if source_module:
                source_modules.append(source_module)
                self.logger.info(f'Found source module "{source_module}" for signal {signal_name}')
            else:
                self.logger.warning(f'Could not extract source module for {signal_name}')

        return source_modules

    def _extract_q_signal(self, verilog_text: str, instance_name: str) -> str:
        # capture the entire instantiation block
        # DOTALL = allow newlines inside (.*?)
        inst_pattern = re.compile(rf'sky130_fd_sc_hd__\w+\s+{re.escape(instance_name)}\s*\((.*?)\);', re.DOTALL)

        inst_match = inst_pattern.search(verilog_text)
        if not inst_match:
            raise RuntimeError(f'Instance {instance_name} not found.')

        inst_block = inst_match.group(1)

        # search for .Q(...)
        q_pattern = re.compile(r'\.Q\s*\(\s*(.*?)\s*\)', re.DOTALL)
        q_match = q_pattern.search(inst_block)
        if not q_match:
            raise RuntimeError(f'.Q port not found for {instance_name}')

        raw_signal = q_match.group(1)

        # cleanup: remove leading backslash, truncate at whitespace or '[' (for verilog arrays, we only care about array variable name, not its size, which is expressed using '[]')
        cleaned = re.sub(r'\\?([^\s\[]+).*', r'\1', raw_signal).strip()

        return cleaned


if __name__ == '__main__':
    generate_yamls_step = GenerateYamls()
    generate_yamls_step.parse_arguments()
    generate_yamls_step.setup()
    generate_yamls_step.step()
