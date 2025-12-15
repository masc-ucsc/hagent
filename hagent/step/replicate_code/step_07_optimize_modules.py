#!/usr/bin/env python3
# See LICENSE for details

from typing import Dict, Tuple, List
import time
import subprocess
import yaml
import os
import importlib.util
from pathlib import Path

from hagent.step.replicate_code.schema import PipelineConfig
from hagent.step.replicate_code.opt_pipe_step_base import OptPipeStepBase
from hagent.tool.extract_code import Extract_code_verilog

synth_path = (Path(__file__).resolve().parent / "../../../scripts/synth.py").resolve()
if not synth_path.exists():
    raise FileNotFoundError(f"synth.py not found at {synth_path}")
spec = importlib.util.spec_from_file_location("synth", synth_path)
if spec is None or spec.loader is None:
    raise ImportError(f"Cannot load spec from {synth_path}")
synth = importlib.util.module_from_spec(spec)
spec.loader.exec_module(synth)


class OptimizeModules(OptPipeStepBase):
    def __init__(self):
        super().__init__()
        self.step_name = 'step_07_optimize_modules'

    def setup(self):
        super().setup()
        self.verilog_extractor = Extract_code_verilog()

    def _synthesize_module(self, code: str, mod_name: str, work_dir: str, liberty_file: str, yosys_cmd: str) -> str:
        """
        Synthesize the given Verilog module using Yosys and generate the netlist.
        Returns the netlist file path, or None if synthesis fails.
        """
        # Create intermediate Verilog file
        verilog_file = os.path.join(work_dir, f'{mod_name}_temp.v')
        with open(verilog_file, 'w') as f:
            f.write(code)

        # Synthesize using Yosys to generate the netlist with liberty file
        netlist_file = os.path.join(work_dir, f'{mod_name}_netlist_temp.v')
        yosys_script = f"""
        read_verilog -sv -defer {verilog_file};
        hierarchy -top {mod_name};
        flatten {mod_name};
        opt;
        synth -top {mod_name};
        dfflibmap -liberty {liberty_file};
        printattrs;
        stat;
        abc -liberty {liberty_file} -dff -keepff -g aig;
        write_verilog {netlist_file};
        """

        try:
            result = subprocess.run(
                [yosys_cmd, '-p', yosys_script],
                capture_output=True,
                text=True,
                check=True,
                timeout=300
            )
            if os.path.exists(netlist_file):
                return netlist_file
            else:
                self.logger.error(f'Netlist file not created for {mod_name}')
                error_msg = (
                    f"Netlist file not created for {mod_name}\n"
                    f"Return code: {result.returncode}\n"
                    f"stdout:\n{result.stdout}\n"
                    f"stderr:\n{result.stderr}"
                )
                raise RuntimeError(error_msg)
        except (subprocess.CalledProcessError, subprocess.TimeoutExpired) as e:
            self.logger.error(f'Error synthesizing {mod_name} with Yosys: {e}')
            raise

    def _extract_arrival_time(self, report_path: str) -> float:
        """Extract the arrival time from the OpenSTA timing report."""
        try:
            with open(report_path, 'r') as file:
                for line in file:
                    if 'data arrival time' in line.lower():
                        # Extract the first number (arrival time) from the line
                        parts = line.split()
                        for part in parts:
                            try:
                                arrival_time = float(part)
                                return arrival_time
                            except ValueError:
                                continue
        except Exception as e:
            self.logger.exception(f'Error reading timing report: {e}')
            raise
        return float('inf')  # Return a large delay if parsing fails

    def _analyze_timing(self, netlist_file: str, mod_name: str, work_dir: str, liberty_file: str, opensta_path: str) -> float:
        """
        Analyze timing using OpenSTA and generate a timing report.
        Returns the arrival time extracted from the report.
        """
        timing_report = os.path.join(work_dir, f'{mod_name}_timing.rpt')
        sta_tcl = os.path.join(work_dir, f'{mod_name}_sta.tcl')

        # Find clock signal in the netlist
        clock_signal = synth.find_clock_signal(netlist_file)

        # Generate OpenSTA TCL script
        tcl_content = f"""read_liberty {liberty_file}
set_units -time ns -capacitance pF -voltage V -current mA -resistance kOhm -distance um
set_operating_conditions ff_100C_1v95
read_verilog {netlist_file}
link_design {mod_name}
"""

        # Add clock constraints if clock signal found
        if clock_signal:
            tcl_content += f"""create_clock -name clk -period 1 {{{clock_signal}}}
set_input_delay -clock clk 0.1 [all_inputs]
set_output_delay -clock clk 0.1 [all_outputs]
"""

        tcl_content += f"""report_checks -path_delay max -unconstrained > {timing_report}
exit
"""

        with open(sta_tcl, 'w') as f:
            f.write(tcl_content)

        # Run OpenSTA with the TCL script
        try:
            result = subprocess.run(
                [opensta_path, sta_tcl],
                capture_output=True,
                text=True,
                timeout=60
            )

            if os.path.exists(timing_report):
                return self._extract_arrival_time(timing_report)
            else:
                error_msg = (
                    f"Timing report not created for {mod_name}\n"
                    f"Return code: {result.returncode}\n"
                    f"stdout:\n{result.stdout}\n"
                    f"stderr:\n{result.stderr}"
                )
                raise RuntimeError(error_msg)
        except (subprocess.CalledProcessError, subprocess.TimeoutExpired) as e:
            self.logger.error(f'Error analyzing timing for {mod_name} with OpenSTA: {e}')
            raise

    def _select_best_variant(
        self, module_name: str, variants: List[str], config: PipelineConfig, work_dir: str
    ) -> Tuple[str, float]:
        """
        Run timing analysis on all variants and select the best one.
        Returns: (best_variant_code, best_arrival_time)
        """
        liberty_file = config.tools.liberty_file
        yosys_cmd = config.tools.yosys_cmd
        opensta_path = config.tools.opensta_path

        best_time = float('inf')
        best_variant = None

        self.logger.info(f'Analyzing {len(variants)} variants for {module_name}')

        for idx, variant in enumerate(variants):
            # Parse the variant (it might be in markdown format)
            parsed_codes = self.verilog_extractor.parse(variant)
            if not parsed_codes or not parsed_codes[0]:
                self.logger.warning(f'Could not parse variant {idx} for {module_name}')
                continue

            code = parsed_codes[0]

            # Synthesize the variant
            netlist_file = self._synthesize_module(code, module_name, work_dir, liberty_file, yosys_cmd)
            if not netlist_file:
                self.logger.warning(f'Synthesis failed for variant {idx} of {module_name}')
                continue

            # Analyze timing
            arrival_time = self._analyze_timing(netlist_file, module_name, work_dir, liberty_file, opensta_path)
            self.logger.info(f'  Variant {idx}: arrival_time = {arrival_time:.2f} ns')

            # Update best if this is better
            if arrival_time < best_time:
                best_time = arrival_time
                best_variant = code

        if best_variant is None:
            self.logger.error(f'No valid variant found for {module_name}')
            return None, float('inf')

        self.logger.info(f'Best variant for {module_name}: arrival_time = {best_time:.2f} ns')
        return best_variant, best_time

    def run(self, data: Dict) -> Dict:
        # Parse input dictionary into typed configuration
        self.config = PipelineConfig.from_dict(data)

        self.prepare_environment(self.config, self.step_name)

        # Get configuration via typed fields
        # Note: generated_input_yamls are populated by step06 in self.config.populated_file_paths
        generated_input_yamls = self.config.populated_file_paths.generated_input_yamls
        results_dir = os.path.join(self.work_dir, "generated_yamls")
        self._prepare_dir(results_dir)

        # Create rtl_optimized directory for storing selected best variants
        rtl_optimized_dir = os.path.join(self.work_dir, "rtl_optimized")
        self._prepare_dir(rtl_optimized_dir)

        if not generated_input_yamls:
            self.error('No YAML files found from previous step')

        # Track optimization results
        optimization_results = []
        total_tokens = 0
        successful_optimizations = 0
        failed_optimizations = 0

        self.logger.info(f'Processing {len(generated_input_yamls)} modules for optimization')

        # Process each YAML file with hagent replicate_code
        for yaml_file in generated_input_yamls:
            if not os.path.exists(yaml_file):
                self.logger.warning(f'Expected generated input YAML file: {yaml_file} not found.')
                continue

            module_name = os.path.basename(yaml_file).replace('.yaml', '')
            module_results_dir = f'{results_dir}/{module_name}'
            os.makedirs(module_results_dir, exist_ok=True)

            module_start_time = time.time()

            # Output files
            output_yaml = f'{module_results_dir}/{module_name}.yaml'
            log_file = f'{module_results_dir}/{module_name}_optimization.log'

            try:
                # Run hagent replicate_code
                cmd = ['uv', 'run', 'python3', f'{self.hagent_root_dir}/hagent/step/replicate_code/replicate_code.py', f'-o{output_yaml}', yaml_file]

                # Change to hagent directory and run
                result = subprocess.run(
                    cmd,
                    cwd=self.hagent_root_dir,
                    capture_output=True,
                    text=True,
                    timeout=1800,  # 30 minute timeout
                )

                module_execution_time = time.time() - module_start_time

                # Save log
                with open(log_file, 'w') as f:
                    f.write(f'Command: {" ".join(cmd)}\n')
                    f.write(f'Return Code: {result.returncode}\n')
                    f.write(f'Execution Time: {module_execution_time:.2f}s\n\n')
                    f.write('STDOUT:\n')
                    f.write(result.stdout)
                    f.write('\n\nSTDERR:\n')
                    f.write(result.stderr)

                # Parse output YAML to extract token usage and variants
                tokens_used = 0
                num_variants = 0
                best_variant_timing = None
                best_variant_file = None

                if result.returncode == 0 and os.path.exists(output_yaml):
                    try:
                        with open(output_yaml, 'r') as f:
                            output_data = yaml.safe_load(f)

                        # Extract token usage from LLM responses
                        if 'replicate_code_response' in output_data:
                            for response in output_data['replicate_code_response']:
                                if isinstance(response, dict) and 'usage' in response:
                                    usage = response['usage']
                                    if 'total_tokens' in usage:
                                        tokens_used += usage['total_tokens']

                        # Extract and validate optimized_equivalent variants
                        variants = output_data.get('optimized_equivalent', [])
                        num_variants = len(variants)

                        if not variants:
                            self.logger.error(f'No LEC-passing variants in optimized_equivalent for {module_name}, will be using the original implementation for synthesis')
                            failed_optimizations += 1
                        else:
                            self.logger.info(f'Found {num_variants} LEC-passing variants for {module_name}')

                            # Run timing analysis to select best variant
                            best_variant_code, best_variant_timing = self._select_best_variant(
                                module_name, variants, self.config, module_results_dir
                            )

                            if best_variant_code:
                                # Save best variant to rtl_optimized directory
                                best_variant_file = os.path.join(rtl_optimized_dir, f'{module_name}.v')
                                with open(best_variant_file, 'w') as f:
                                    f.write(best_variant_code)
                                self.logger.info(f'Saved best variant to {best_variant_file}')
                                successful_optimizations += 1
                            else:
                                self.logger.error(f'Failed to select best variant for {module_name}')
                                failed_optimizations += 1

                    except Exception as e:
                        self.logger.error(f'Error processing output YAML for {module_name}: {e}')
                        failed_optimizations += 1
                else:
                    failed_optimizations += 1

                total_tokens += tokens_used

                optimization_results.append(
                    {
                        'module_name': module_name,
                        'input_yaml': yaml_file,
                        'output_yaml': output_yaml,
                        'log_file': log_file,
                        'return_code': result.returncode,
                        'execution_time': module_execution_time,
                        'tokens_used': tokens_used,
                        'success': result.returncode == 0 and best_variant_file is not None,
                        'num_variants': num_variants,
                        'best_variant_timing': best_variant_timing,
                        'best_variant_file': best_variant_file,
                    }
                )

            except subprocess.TimeoutExpired:
                module_execution_time = time.time() - module_start_time
                with open(log_file, 'w') as f:
                    f.write(f'Command: {" ".join(cmd)}\n')
                    f.write(f'Status: TIMEOUT after {module_execution_time:.2f}s\n')

                optimization_results.append(
                    {
                        'module_name': module_name,
                        'input_yaml': yaml_file,
                        'output_yaml': output_yaml,
                        'log_file': log_file,
                        'return_code': -1,
                        'execution_time': module_execution_time,
                        'tokens_used': 0,
                        'success': False,
                        'num_variants': 0,
                        'best_variant_timing': None,
                        'best_variant_file': None,
                    }
                )
                failed_optimizations += 1

            except Exception as e:
                module_execution_time = time.time() - module_start_time
                with open(log_file, 'w') as f:
                    f.write(f'Command: {" ".join(cmd)}\n')
                    f.write(f'Error: {str(e)}\n')
                    f.write(f'Execution Time: {module_execution_time:.2f}s\n')

                optimization_results.append(
                    {
                        'module_name': module_name,
                        'input_yaml': yaml_file,
                        'output_yaml': output_yaml,
                        'log_file': log_file,
                        'return_code': -2,
                        'execution_time': module_execution_time,
                        'tokens_used': 0,
                        'success': False,
                        'num_variants': 0,
                        'best_variant_timing': None,
                        'best_variant_file': None,
                    }
                )
                failed_optimizations += 1

        # Store execution metadata locally for debugging
        debug_log = f'{self.step_debug_dir}/execution_log.txt'
        self.logger.info(f'Writing debug log to {debug_log}')
        with open(debug_log, 'w') as f:
            f.write('Step 07 - Optimize Modules with Hagent\n')
            f.write(f'Execution Time: {time.time() - self.start_time:.2f}s\n')
            f.write(f'Benchmark: {self.config.benchmark.name}\n')
            f.write(f'Modules Processed: {len(optimization_results)}\n')
            f.write(f'Successful Optimizations: {successful_optimizations}\n')
            f.write(f'Failed Optimizations: {failed_optimizations}\n')
            f.write(f'Total Tokens Used: {total_tokens}\n')
            f.write(f'Results Directory: {results_dir}\n\n')

            for result in optimization_results:
                f.write(f'Module: {result["module_name"]}\n')
                f.write(f'  Success: {result["success"]}\n')
                f.write(f'  Time: {result["execution_time"]:.2f}s\n')
                f.write(f'  Tokens: {result["tokens_used"]}\n')
                f.write(f'  Return Code: {result["return_code"]}\n')
                f.write(f'  Variants: {result["num_variants"]}\n')
                if result["best_variant_timing"]:
                    f.write(f'  Best Variant Timing: {result["best_variant_timing"]:.2f} ns\n')
                if result["best_variant_file"]:
                    f.write(f'  Best Variant File: {result["best_variant_file"]}\n')
                f.write('\n')

        self.step_results['optimization_results'] = optimization_results
        self.step_results['summary'] = {
            'modules_processed': len(optimization_results),
            'successful_optimizations': successful_optimizations,
            'failed_optimizations': failed_optimizations,
            'total_tokens_used': total_tokens,
        }

        # Update metrics in config
        self.config.metrics.modules_optimized = optimization_results

        # Store rtl_optimized directory in populated_file_paths for step_08
        self.config.populated_file_paths.optimized_dir = rtl_optimized_dir

        # Store execution time and results
        self.step_results['execution_time'] = time.time() - self.start_time
        self.step_results['success'] = successful_optimizations > 0

        # Save step results to file and store reference in config
        results_file = self.save_step_results()
        self.config.step_results[self.step_name] = {'results_file': results_file}

        # Convert back to dict for pipeline compatibility
        return self.config.to_dict()


if __name__ == '__main__':
    optimize_modules_step = OptimizeModules()
    optimize_modules_step.parse_arguments()
    optimize_modules_step.setup()
    optimize_modules_step.step()
