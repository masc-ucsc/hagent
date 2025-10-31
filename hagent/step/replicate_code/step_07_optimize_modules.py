#!/usr/bin/env python3
# See LICENSE for details

from hagent.inou.runner import Runner
from hagent.core.step import Step
from typing import Dict
import os
import time
import subprocess
import yaml


class OptimizeModules(Step):
    def setup(self):
        super().setup()

    def run(self, data: Dict):
        data_copy = data.copy()
        start_time = time.time()

        # Extract configuration from input YAML
        benchmark = data_copy.get('benchmark', {})
        local_storage = data_copy.get('local_storage', {})

        # Create debug directory
        cache_dir = os.getenv('HAGENT_CACHE_DIR', local_storage.get('debug_base_dir', '/tmp/rtl_optimization_debug'))
        timestamp = str(int(time.time()))
        step_debug_dir = f"{cache_dir}/step07_optimize_modules_{timestamp}"
        os.makedirs(step_debug_dir, exist_ok=True)

        step_results = {
            'start_time': start_time,
            'debug_directory': step_debug_dir,
            'timestamp': timestamp
        }

        # Get configuration
        generated_yamls = data_copy.get('file_paths', {}).get('generated_yamls', [])
        results_dir = data_copy.get('file_paths', {}).get('results_dir')

        if not generated_yamls:
            self.error("No YAML files found from previous step")
            return data_copy

        # Track optimization results
        optimization_results = []
        total_tokens = 0
        successful_optimizations = 0
        failed_optimizations = 0

        # Process each YAML file with hagent replicate_code
        for yaml_file in generated_yamls:
            if not os.path.exists(yaml_file):
                continue

            module_name = os.path.basename(yaml_file).replace('.yaml', '')
            module_results_dir = f"{results_dir}/{module_name}"
            os.makedirs(module_results_dir, exist_ok=True)

            module_start_time = time.time()

            # Output files
            output_yaml = f"{module_results_dir}/{module_name}.yaml"
            log_file = f"{module_results_dir}/{module_name}_optimization.log"

            try:
                # Run hagent replicate_code
                cmd = [
                    'uv', 'run', 'python3',
                    './hagent/step/replicate_code/replicate_code.py',
                    f'-o{output_yaml}',
                    yaml_file
                ]

                # Change to hagent directory and run
                hagent_dir = '/home/sgarg3/hagent'
                result = subprocess.run(
                    cmd,
                    cwd=hagent_dir,
                    capture_output=True,
                    text=True,
                    timeout=1800  # 30 minute timeout
                )

                module_execution_time = time.time() - module_start_time

                # Save log
                with open(log_file, 'w') as f:
                    f.write(f"Command: {' '.join(cmd)}\n")
                    f.write(f"Return Code: {result.returncode}\n")
                    f.write(f"Execution Time: {module_execution_time:.2f}s\n\n")
                    f.write("STDOUT:\n")
                    f.write(result.stdout)
                    f.write("\n\nSTDERR:\n")
                    f.write(result.stderr)

                # Parse output YAML to extract token usage
                tokens_used = 0
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
                    except Exception as e:
                        pass  # Continue if YAML parsing fails

                    successful_optimizations += 1
                else:
                    failed_optimizations += 1

                total_tokens += tokens_used

                optimization_results.append({
                    'module_name': module_name,
                    'input_yaml': yaml_file,
                    'output_yaml': output_yaml,
                    'log_file': log_file,
                    'return_code': result.returncode,
                    'execution_time': module_execution_time,
                    'tokens_used': tokens_used,
                    'success': result.returncode == 0
                })

            except subprocess.TimeoutExpired:
                module_execution_time = time.time() - module_start_time
                with open(log_file, 'w') as f:
                    f.write(f"Command: {' '.join(cmd)}\n")
                    f.write(f"Status: TIMEOUT after {module_execution_time:.2f}s\n")

                optimization_results.append({
                    'module_name': module_name,
                    'input_yaml': yaml_file,
                    'output_yaml': output_yaml,
                    'log_file': log_file,
                    'return_code': -1,
                    'execution_time': module_execution_time,
                    'tokens_used': 0,
                    'success': False
                })
                failed_optimizations += 1

            except Exception as e:
                module_execution_time = time.time() - module_start_time
                with open(log_file, 'w') as f:
                    f.write(f"Command: {' '.join(cmd)}\n")
                    f.write(f"Error: {str(e)}\n")
                    f.write(f"Execution Time: {module_execution_time:.2f}s\n")

                optimization_results.append({
                    'module_name': module_name,
                    'input_yaml': yaml_file,
                    'output_yaml': output_yaml,
                    'log_file': log_file,
                    'return_code': -2,
                    'execution_time': module_execution_time,
                    'tokens_used': 0,
                    'success': False
                })
                failed_optimizations += 1

        # Store execution metadata locally for debugging
        debug_log = f"{step_debug_dir}/execution_log.txt"
        with open(debug_log, 'w') as f:
            f.write(f"Step 07 - Optimize Modules with Hagent\n")
            f.write(f"Execution Time: {time.time() - start_time:.2f}s\n")
            f.write(f"Benchmark: {benchmark.get('name', 'Unknown')}\n")
            f.write(f"Modules Processed: {len(optimization_results)}\n")
            f.write(f"Successful Optimizations: {successful_optimizations}\n")
            f.write(f"Failed Optimizations: {failed_optimizations}\n")
            f.write(f"Total Tokens Used: {total_tokens}\n")
            f.write(f"Results Directory: {results_dir}\n\n")

            for result in optimization_results:
                f.write(f"Module: {result['module_name']}\n")
                f.write(f"  Success: {result['success']}\n")
                f.write(f"  Time: {result['execution_time']:.2f}s\n")
                f.write(f"  Tokens: {result['tokens_used']}\n")
                f.write(f"  Return Code: {result['return_code']}\n\n")

        step_results['optimization_results'] = optimization_results
        step_results['summary'] = {
            'modules_processed': len(optimization_results),
            'successful_optimizations': successful_optimizations,
            'failed_optimizations': failed_optimizations,
            'total_tokens_used': total_tokens
        }

        # Update metrics
        if 'metrics' not in data_copy:
            data_copy['metrics'] = {}
        data_copy['metrics']['modules_optimized'] = optimization_results
        data_copy['metrics']['total_tokens_used'] = total_tokens

        # Store execution time and results
        step_results['execution_time'] = time.time() - start_time
        step_results['success'] = successful_optimizations > 0

        if 'step_results' not in data_copy:
            data_copy['step_results'] = {}
        data_copy['step_results']['step_07_optimize_modules'] = step_results

        return data_copy


if __name__ == '__main__':
    optimize_modules_step = OptimizeModules()
    optimize_modules_step.parse_arguments()
    optimize_modules_step.setup()
    optimize_modules_step.step()