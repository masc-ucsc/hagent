#!/usr/bin/env python3
# See LICENSE for details

from typing import Dict
from pathlib import Path
import os
import shutil
import time
import yaml

from hagent.step.replicate_code.schema import PipelineConfig
from hagent.step.replicate_code.opt_pipe_step_base import OptPipeStepBase


class GenerateYamls(OptPipeStepBase):
    """Gathers all Verilog modules from the target RTL directory and create YAML configuration files for each module as HAgent input."""
    def __init__(self):
        super().__init__()
        self.step_name = 'step_06_generate_yamls'

    def setup(self):
        super().setup()

    def _run_impl(self, data: Dict):
        # Parse input dictionary into typed configuration
        config = PipelineConfig.from_dict(data)

        self.prepare_environment(config, self.step_name)
        assert self.runner is not None

        input_yamls_dir = config.local_storage.input_yamls_dir
        # Create directories locally (outside docker)
        collected_input_yamls_dir = os.path.join(self.work_dir, "input_yamls")
        self._prepare_dir(collected_input_yamls_dir)
        for item in Path(input_yamls_dir).expanduser().resolve().iterdir():
            if item.is_file() and item.suffix in {".yaml", "yml"}:
                shutil.copy2(item, Path(collected_input_yamls_dir) / item.name)

        # Find .v files from liveparse directory
        rtl_modules_dir = config.populated_file_paths.rtl_path
        self.logger.info(f'Finding module files in {rtl_modules_dir}/liveparse')
        ret, out, err = self.runner.run_cmd(f'find {rtl_modules_dir}/liveparse -name "*.v" -type f | sort', quiet=True)
        if ret != 0:
            self.logger.error('Failed to find module files!')
            self.logger.error(f'STDOUT:\n{out}')
            self.logger.error(f'STDERR:\n{err}')
            self.error(f'Failed to find module files in {rtl_modules_dir}/liveparse: {err}')
        module_files = [f.strip() for f in out.split('\n') if f.strip()] if out else []
        self.step_results['module_discovery'] = {'ret': ret, 'stdout': out, 'stderr': err, 'module_files': module_files}

        model = config.optimization.model
        run_with_synalign = config.optimization.run_with_synalign

        generated_yamls = []
        modules_processed = []

        # Process each module file splitted in step 3
        for module_file in module_files:
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
                yaml_content['threshold'] = config.optimization.threshold
            elif 'o4' in model:
                yaml_content['temperature'] = config.optimization.threshold

            # Save YAML file locally
            yaml_filename = f'{module_name}.yaml'
            local_yaml_path = f'{collected_input_yamls_dir}/{yaml_filename}'

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
        config.populated_file_paths.generated_input_yamls = generated_yamls

        self.logger.info(f'Generated {len(generated_yamls)} YAML files for optimization')

        # Store execution metadata locally for debugging
        debug_log = f'{self.step_debug_dir}/execution_log.txt'
        self.logger.info(f'Writing debug log to {debug_log}')
        with open(debug_log, 'w') as f:
            f.write('Step 06 - Generate YAML Files for Optimization\n')
            f.write(f'Execution Time: {time.time() - self.start_time:.2f}s\n')
            f.write(f'Benchmark: {config.benchmark.name}\n')
            f.write(f'Model: {model}\n')
            f.write(f'Run with SynAlign: {run_with_synalign}\n')
            f.write(f'Input YAMLs Directory: {collected_input_yamls_dir}\n')
            f.write(f'Modules Processed: {len(modules_processed)}\n')
            f.write(f'Number of YAML Files Generated: {len(generated_yamls)}\n')
            for i, module_info in enumerate(modules_processed):
                f.write(f'  {i + 1}. {module_info["module_name"]}: {module_info["yaml_file"]}\n')

        # Store execution time and results
        self.step_results['execution_time'] = time.time() - self.start_time
        self.step_results['success'] = len(generated_yamls) > 0

        # Save step results to file and store reference in config
        results_file = self.save_step_results()
        config.step_results[self.step_name] = {'results_file': results_file}

        # Convert back to dict for pipeline compatibility
        return config.to_dict()


if __name__ == '__main__':
    generate_yamls_step = GenerateYamls()
    generate_yamls_step.parse_arguments()
    generate_yamls_step.setup()
    generate_yamls_step.step()
