#!/usr/bin/env python3
# See LICENSE for details

from hagent.inou.runner import Runner
from hagent.core.step import Step
from typing import Dict
import os
import time
import yaml


class GenerateYamls(Step):
    def setup(self):
        super().setup()

    def run(self, data: Dict):
        data_copy = data.copy()
        start_time = time.time()

        # Extract configuration from input YAML
        benchmark = data_copy.get('benchmark', {})
        docker_config = data_copy.get('docker', {})
        local_storage = data_copy.get('local_storage', {})
        optimization = data_copy.get('optimization', {})

        # Setup runner with docker image from config
        if os.getenv('HAGENT_EXECUTION_MODE') == 'docker':
            docker_image = docker_config.get('image')
            self.runner = Runner(docker_image=docker_image)
        else:
            self.runner = Runner()

        if not self.runner.setup():
            self.error(f'OOPS in step_06_generate_yamls.py error from runner:{self.runner.get_error()}')
            return data_copy

        # Create debug directory
        cache_dir = os.getenv('HAGENT_CACHE_DIR', local_storage.get('debug_base_dir', '/tmp/rtl_optimization_debug'))
        timestamp = str(int(time.time()))
        step_debug_dir = f"{cache_dir}/step06_generate_yamls_{timestamp}"
        os.makedirs(step_debug_dir, exist_ok=True)

        step_results = {
            'start_time': start_time,
            'debug_directory': step_debug_dir,
            'timestamp': timestamp
        }

        # Get configuration
        split_module_files = data_copy.get('file_paths', {}).get('split_module_files', [])
        input_yamls_dir = local_storage.get('input_yamls_dir', '/home/sgarg3/hagent/hagent/step/replicate_code/tests/input_yamls')
        results_dir = local_storage.get('results_dir', '/home/sgarg3/hagent/generated_yamls')
        model = optimization.get('model', 'openai/o3-mini-2025-01-31')
        run_with_synalign = optimization.get('run_with_synalign', False)

        # Create directories locally (outside docker)
        os.makedirs(input_yamls_dir, exist_ok=True)
        os.makedirs(results_dir, exist_ok=True)

        # Find .v files from liveparse directory
        rtl_modules_dir = data_copy.get('file_paths', {}).get('rtl_modules_dir', '/tmp/rtl_modules')
        ret, out, err = self.runner.run(f'find {rtl_modules_dir}/liveparse -name "*.v" -type f | sort')

        if ret != 0:
            self.error(f"Failed to find module files in {rtl_modules_dir}/liveparse: {err}")
            return data_copy

        module_files = [f.strip() for f in out.split('\n') if f.strip()] if out else []
        step_results['module_discovery'] = {
            'ret': ret, 'stdout': out, 'stderr': err,
            'module_files': module_files
        }

        generated_yamls = []
        modules_processed = []

        # Process each module file
        for module_file in module_files:
            if not module_file:
                continue

            # Extract module name
            module_name = os.path.basename(module_file).replace('.v', '')

            # Read module content
            ret, module_content, err = self.runner.run(f'cat {module_file}')
            if ret != 0:
                continue

            # Create YAML content using the same structure as create_yaml_for_hagent.py
            yaml_content = {
                "replicate_code_prompt1": [
                    {
                        "role": "system",
                        "content": (
                            "You are a super smart Verilog and timing expert. "
                            "You have been tasked with improving the frequency of a verilog code. "
                            "You provide a higher frequency code which passes LEC. "
                            "Make sure that you only return the code that passes LEC. "
                            "Take care that: "
                            "The semantics are preserved exactly as in the original netlist (including word instantiation and sign‐extension) "
                            "while breaking a long combinational critical path. "
                            "The resultant code is functionally equivalent to the original and passes LEC."
                        )
                    },
                    {
                        "role": "user",
                        "content": (
                            f"This is the current Verilog:\n```\n{module_content}\n```\n"
                            "Please do not change semantics, just split the always blocks in separate always blocks "
                            "and try to improve the performance when possible."
                        )
                    }
                ],
                "top_name": module_name,
                "llm": {"model": model},
                "code_content": module_content
            }

            # Add threshold for o3 models
            if "o3" in model:
                yaml_content["threshold"] = optimization.get('threshold', 40)
            elif "o4" in model:
                yaml_content["temperature"] = optimization.get('threshold', 40)

            # Save YAML file locally
            yaml_filename = f"{module_name}.yaml"
            local_yaml_path = f"{input_yamls_dir}/{yaml_filename}"

            with open(local_yaml_path, 'w') as f:
                yaml.dump(yaml_content, f, default_flow_style=False, sort_keys=False, allow_unicode=True, indent=2)

            generated_yamls.append(local_yaml_path)
            modules_processed.append({
                'module_name': module_name,
                'source_file': module_file,
                'yaml_file': local_yaml_path
            })

        step_results['yaml_generation'] = {
            'modules_processed': len(modules_processed),
            'yamls_generated': generated_yamls,
            'modules_info': modules_processed
        }

        # Store execution metadata locally for debugging
        debug_log = f"{step_debug_dir}/execution_log.txt"
        with open(debug_log, 'w') as f:
            f.write(f"Step 06 - Generate YAML Files for Optimization\n")
            f.write(f"Execution Time: {time.time() - start_time:.2f}s\n")
            f.write(f"Benchmark: {benchmark.get('name', 'Unknown')}\n")
            f.write(f"Model: {model}\n")
            f.write(f"Run with SynAlign: {run_with_synalign}\n")
            f.write(f"Input YAMLs Directory: {input_yamls_dir}\n")
            f.write(f"Results Directory: {results_dir}\n")
            f.write(f"Modules Processed: {len(modules_processed)}\n")
            f.write(f"YAML Files Generated: {len(generated_yamls)}\n")
            for i, module_info in enumerate(modules_processed):
                f.write(f"  {i+1}. {module_info['module_name']}: {module_info['yaml_file']}\n")

        # Update file paths
        if 'file_paths' not in data_copy:
            data_copy['file_paths'] = {}
        data_copy['file_paths']['input_yamls_dir'] = input_yamls_dir
        data_copy['file_paths']['results_dir'] = results_dir
        data_copy['file_paths']['generated_yamls'] = generated_yamls

        # Store execution time and results
        step_results['execution_time'] = time.time() - start_time
        step_results['success'] = len(generated_yamls) > 0

        if 'step_results' not in data_copy:
            data_copy['step_results'] = {}
        data_copy['step_results']['step_06_generate_yamls'] = step_results

        return data_copy


if __name__ == '__main__':
    generate_yamls_step = GenerateYamls()
    generate_yamls_step.parse_arguments()
    generate_yamls_step.setup()
    generate_yamls_step.step()