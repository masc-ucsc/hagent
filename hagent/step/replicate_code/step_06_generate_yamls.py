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
        self.logger.info(f'Finding module files in {rtl_modules_dir}')
        ret, out, err = self.runner.run_cmd(f'find {rtl_modules_dir} -name "*.v" -o -name "*.sv" -type f | sort', quiet=True)
        if ret != 0:
            self.logger.error('Failed to find module files!')
            self.logger.error(f'STDOUT:\n{out}')
            self.logger.error(f'STDERR:\n{err}')
            self.error(f'Failed to find module files in {rtl_modules_dir}/liveparse: {err}')

        critical_path_modules = self._locate_module_names_with_timing_rpt(self.config.populated_file_paths.timing_report_file)
        module_files = [f.strip() for f in out.split('\n') if f.strip()] if out else []
        self.step_results['module_discovery'] = {'ret': ret, 'stdout': out, 'stderr': err, 'module_files': module_files}
        self.step_results['critical_path_modules'] = critical_path_modules

        # Parse module hierarchy and expand critical modules to include ancestors up to LCA
        hierarchy = self._parse_module_hierarchy(f'{rtl_modules_dir}')
        self.step_results['module_hierarchy'] = hierarchy

        # Expand critical modules to include parent modules up to LCA
        top_module = self.config.benchmark.top_module
        modules_to_optimize = self._collect_modules_to_optimize(critical_path_modules, hierarchy, top_module)
        self.step_results['modules_to_optimize'] = modules_to_optimize
        self.logger.info(
            f'Expanded critical modules {critical_path_modules} to {modules_to_optimize} (including ancestors up to LCA)'
        )

        model = self.config.optimization.model
        run_with_synalign = self.config.optimization.run_with_synalign

        generated_yamls = []
        modules_processed = []

        # Process each module file for modules in the expanded set
        critical_path_module_files = [path for path in module_files if any(mod in path for mod in modules_to_optimize)]

        for module_file in critical_path_module_files:
            if not module_file:
                continue

            # Extract module name
            module_name = os.path.splitext(os.path.basename(module_file))[0]

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
            f.write(f'Top Module: {top_module}\n')
            f.write(f'Critical Path Modules (initial): {critical_path_modules}\n')
            f.write(f'Modules to Optimize (after hierarchy expansion): {modules_to_optimize}\n')
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
            result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, check=False)

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

    def _extract_module_name_from_verilog_file(self, file_path: str) -> Optional[str]:
        """
        Extract the module name from a Verilog source file.

        This function parses the source Verilog file to find the module declaration
        and extracts the module name. It handles both Verilog (.v) and SystemVerilog (.sv) files.

        Strategies:
        1. Parse the file to find "module ModuleName(" declaration
        2. Fall back to extracting from filename if parsing fails

        Args:
            file_path: Path to the Verilog source file

        Returns:
            Module name (e.g., "Adder") or None if not found
        """
        try:
            with open(file_path, 'r') as f:
                content = f.read()

            # Find module declaration in the file
            # Pattern: module ModuleName ( or module ModuleName#( (for parameterized modules)
            module_pattern = re.compile(r'^\s*module\s+(\w+)\s*[#(]', re.MULTILINE)
            match = module_pattern.search(content)

            if match:
                module_name = match.group(1)
                self.logger.debug(f'Extracted module name "{module_name}" from module declaration in {file_path}')
                return module_name

            # Extract from filename as fallback (this assumes filename convention: ModuleName.v or ModuleName.sv)
            basename = os.path.basename(file_path)
            module_name = os.path.splitext(basename)[0]
            self.logger.debug(f'Extracted module name "{module_name}" from filename {file_path}')
            return module_name

        except Exception as e:
            self.logger.error(f'Error reading Verilog file {file_path}: {e}')
            return None

    def _locate_module_names_with_timing_rpt(self, timing_report: str | Path) -> List[str]:
        """
        Get the source module names that constitute the critical path.

        This method:
        1. Parses timing report to extract launch/capture flip-flop instances
        2. Extracts Q/D signal names from the synthesized netlist
        3. Invokes cli_locator to find VCD signal locations in source Verilog files
        4. Extracts module names from the source Verilog files

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
        capture_d_signal = self._extract_q_signal(verilog_text, capture[0])

        self.logger.info(f'Launch Q signal: {launch_q_signal}')
        self.logger.info(f'Capture D signal: {capture_d_signal}')

        # Construct full VCD hierarchical paths and find source modules
        source_modules = []
        top_module = self.config.benchmark.top_module

        for signal_name in [launch_q_signal, capture_d_signal]:
            # Construct full hierarchical VCD path: TopModule.signal.name
            vcd_path = f'{top_module}.{signal_name}'
            self.logger.debug(f'Looking up VCD path: {vcd_path}')

            # Invoke cli_locator to find netlist locations
            locations = self._invoke_locator(vcd_path)

            if not locations:
                self.logger.warning(f'No locations found for {vcd_path}')
                continue

            # Extract source module from first location
            file_path, _ = locations[0]
            source_module = self._extract_module_name_from_verilog_file(file_path)

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

    def _parse_module_hierarchy(self, liveparse_dir: str) -> Dict[str, List[str]]:
        """
        Parse Verilog files to build module hierarchy.

        Returns:
            Dictionary mapping parent module -> list of child modules it instantiates
        """
        hierarchy = {}  # parent -> [children]

        # Find all .v files
        ret, out, err = self.runner.run_cmd(f'find {liveparse_dir} -name "*.v" -type f | sort', quiet=True)
        if ret != 0:
            self.logger.error(f'Failed to find .v files in {liveparse_dir}')
            return hierarchy

        module_files = [f.strip() for f in out.split('\n') if f.strip()]

        # Pattern to match module instantiations: ModuleType instance_name (
        # Matches patterns like: StageReg_6 mem_wb_ctrl (
        inst_pattern = re.compile(r'^\s*(\w+)\s+\w+\s*\(', re.MULTILINE)

        for module_file in module_files:
            # Extract module name from filename
            parent_module = os.path.basename(module_file).replace('.v', '')

            # Read module content
            ret, content, err = self.runner.run_cmd(f'cat {module_file}; echo', quiet=True)
            if ret != 0:
                self.logger.warning(f'Failed to read {module_file}')
                continue

            # Find all module instantiations
            child_modules = set()
            for match in inst_pattern.finditer(content):
                module_type = match.group(1)
                # Filter out Verilog keywords and wire/reg declarations
                if module_type not in [
                    'module',
                    'input',
                    'output',
                    'wire',
                    'reg',
                    'assign',
                    'always',
                    'begin',
                    'end',
                    'if',
                    'else',
                ]:
                    child_modules.add(module_type)

            hierarchy[parent_module] = list(child_modules)
            self.logger.debug(f'Module {parent_module} instantiates: {child_modules}')

        return hierarchy

    def _build_parent_map(self, hierarchy: Dict[str, List[str]]) -> Dict[str, List[str]]:
        """
        Build reverse mapping: child -> list of parents that instantiate it.

        Args:
            hierarchy: parent -> [children] mapping

        Returns:
            Dictionary mapping child module -> list of parent modules
        """
        parent_map = {}

        for parent, children in hierarchy.items():
            for child in children:
                if child not in parent_map:
                    parent_map[child] = []
                parent_map[child].append(parent)

        return parent_map

    def _find_path_to_root(self, module: str, parent_map: Dict[str, List[str]], top_module: str) -> List[str]:
        """
        Find path from a module to the top module.

        Args:
            module: Starting module
            parent_map: child -> [parents] mapping
            top_module: Root/top module name

        Returns:
            List representing path from module to top (inclusive), or empty list if no path found
        """
        if module == top_module:
            return [top_module]

        if module not in parent_map:
            self.logger.warning(f'Module {module} has no parents')
            return []

        # For simplicity, take the first parent (assumes tree structure, not DAG)
        # In a full implementation, we might need to handle multiple paths
        visited = set()
        path = [module]
        current = module

        while current != top_module:
            if current in visited:
                self.logger.warning(f'Cycle detected in hierarchy at {current}')
                return []

            visited.add(current)

            if current not in parent_map or len(parent_map[current]) == 0:
                self.logger.warning(f'Module {current} has no path to top module {top_module}')
                return []

            # Take first parent
            parent = parent_map[current][0]
            path.append(parent)
            current = parent

        return path

    def _find_lca(self, modules: List[str], parent_map: Dict[str, List[str]], top_module: str) -> Optional[str]:
        """
        Find the Lowest Common Ancestor (LCA) of a list of modules.

        Args:
            modules: List of module names
            parent_map: child -> [parents] mapping
            top_module: Root/top module name

        Returns:
            LCA module name, or None if not found
        """
        if not modules:
            return None

        if len(modules) == 1:
            # Single module: return its parent (or itself if it's the top)
            module = modules[0]
            if module == top_module:
                return None  # Can't optimize top module
            if module in parent_map and parent_map[module]:
                return parent_map[module][0]
            return None

        # Find paths to root for all modules
        paths = []
        for module in modules:
            path = self._find_path_to_root(module, parent_map, top_module)
            if not path:
                self.logger.warning(f'Could not find path to root for module {module}')
                return None
            paths.append(path)

        # Convert paths to sets for easier intersection
        # The LCA is the first common ancestor when traversing from leaf to root
        # We'll find it by checking each level
        min_path_len = min(len(p) for p in paths)

        # Start from the end (top module) and work backwards
        for i in range(min_path_len):
            # Check if all paths have the same module at this level from the end
            ancestors = [path[-(i + 1)] for path in paths]
            if len(set(ancestors)) == 1:
                # All have same ancestor at this level, but keep looking for closer one
                lca_candidate = ancestors[0]
            else:
                # Divergence found, return the last common ancestor
                # If i == 0, paths diverge immediately at top, return top
                if i == 0:
                    return top_module
                return lca_candidate

        # All paths are identical up to min length
        return paths[0][-min_path_len]

    def _collect_modules_to_optimize(
        self, critical_modules: List[str], hierarchy: Dict[str, List[str]], top_module: str
    ) -> List[str]:
        """
        Collect all modules to optimize: critical modules + their ancestors up to LCA (excluding top).

        Args:
            critical_modules: Initial critical path modules
            hierarchy: parent -> [children] mapping
            top_module: Top module to exclude

        Returns:
            List of module names to optimize
        """
        if not critical_modules:
            return []

        parent_map = self._build_parent_map(hierarchy)

        # Find LCA
        lca = self._find_lca(critical_modules, parent_map, top_module)

        if lca is None:
            self.logger.warning('Could not find LCA, using only critical modules')
            return critical_modules

        if lca == top_module:
            self.logger.warning('LCA is top module, excluding it from optimization')
            # Collect all modules from critical modules up to (but excluding) top
            modules_to_optimize = set(critical_modules)
            for module in critical_modules:
                path = self._find_path_to_root(module, parent_map, top_module)
                # Add all modules in path except the top
                modules_to_optimize.update([m for m in path if m != top_module])
            return list(modules_to_optimize)

        self.logger.info(f'LCA of critical modules {critical_modules} is: {lca}')

        # Collect all modules from critical modules to LCA (inclusive)
        modules_to_optimize = set(critical_modules)
        modules_to_optimize.add(lca)  # Include LCA

        for module in critical_modules:
            path = self._find_path_to_root(module, parent_map, top_module)
            # Add all modules from current to LCA
            for m in path:
                if m == top_module:
                    break
                modules_to_optimize.add(m)
                if m == lca:
                    break

        result = list(modules_to_optimize)
        self.logger.info(f'Modules to optimize (critical + ancestors to LCA): {result}')
        return result


if __name__ == '__main__':
    generate_yamls_step = GenerateYamls()
    generate_yamls_step.parse_arguments()
    generate_yamls_step.setup()
    generate_yamls_step.step()
