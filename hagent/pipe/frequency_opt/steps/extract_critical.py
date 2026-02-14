# See LICENSE for details
"""
Extract Critical Path step: identifies RTL modules on the critical path.

This step analyzes the timing report to find which modules contribute
to the critical path, then uses LCA (Lowest Common Ancestor) to determine
which modules should be optimized.
"""

import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from hagent.core.step import Step
from hagent.pipe.frequency_opt.schema import (
    BenchmarkConfig,
    RTLSourceConfig,
    StorageConfig,
    ToolsConfig,
    require_field,
    set_field,
)


class ExtractCriticalStep(Step):
    """
    Extract critical path modules step.

    Required YAML sections:
      - benchmark: top_module
      - rtl: source_dir
      - storage: output_dir

    Required YAML fields (from previous steps):
      - sta.report_path
      - synthesis.netlist_path

    Writes to YAML:
      - critical_path_info.dir: Directory containing copied RTL files
      - critical_path_info.module_names: List of module names to optimize
      - critical_path_info.critical_path: Info for critical path,such as start/end flops
    """

    def __init__(self):
        super().__init__()
        # Instance fields to store configuration - accessible by all helper methods
        self.benchmark: Optional[BenchmarkConfig] = None
        self.rtl: Optional[RTLSourceConfig] = None
        self.storage: Optional[StorageConfig] = None
        self.netlist_path: Optional[Path] = None
        self.report_path: Optional[Path] = None
        self.rtl_dir: Optional[Path] = None

    def run(self, data: Dict) -> Dict:
        # Parse configuration and store as instance fields
        self.benchmark = BenchmarkConfig.from_data(data, 'benchmark')
        self.rtl = RTLSourceConfig.from_data(data, 'rtl')
        self.storage = StorageConfig.from_data(data, 'storage')

        # Get paths from previous steps
        self.report_path = Path(require_field(data, 'sta.report_path'))
        self.netlist_path = Path(require_field(data, 'synthesis.netlist_path'))
        self.rtl_dir = Path(self.rtl.source_dir)

        # Validate paths exist
        if not self.report_path.exists():
            self.error(f'Timing report not found: {self.report_path}')
        if not self.netlist_path.exists():
            self.error(f'Netlist not found: {self.netlist_path}')

        print('Extracting critical path modules:')
        print(f'  Timing report: {self.report_path}')
        print(f'  Netlist: {self.netlist_path}')
        print(f'  RTL source: {self.rtl_dir}')

        # Step 1: Extract critical path module names from timing report
        critical_path_modules, start_flop, end_flop = self._locate_modules_and_launch_capture_flops()
        print(f'  Critical path modules: {critical_path_modules}')

        # Optional: Run synalign for full net mapping
        tools = ToolsConfig.from_data_optional(data, 'tools')
        synalign_mapping = None
        if tools and tools.run_synalign:
            synalign_mapping = self._run_synalign(data, tools, critical_path_modules)

        # Step 2: Parse module hierarchy from RTL files
        hierarchy = self._parse_module_hierarchy()
        print(f'  Found {len(hierarchy)} modules in hierarchy')

        # Step 3: Expand critical modules to include ancestors up to LCA
        modules_to_optimize, lca = self._collect_modules_to_optimize(critical_path_modules, hierarchy)
        print(f'  LCA: {lca}')
        print(f'  Modules to optimize: {modules_to_optimize}')

        # Step 4: Map modules to their RTL files
        module_to_file = self._map_modules_to_files()

        # Step 5: Copy relevant RTL files to working directory
        work_dir = Path(self.storage.output_dir) / 'critical_modules'
        if os.path.exists(work_dir):
            shutil.rmtree(work_dir)
            print('  Removed existing critical modules dir')
        os.makedirs(work_dir)

        copied_files = []
        for module_name in modules_to_optimize:
            if module_name in module_to_file:
                src_file = module_to_file[module_name]
                dst_file = work_dir / src_file.name
                shutil.copy2(src_file, dst_file)
                copied_files.append(str(dst_file))
                print(f'  Copied: {src_file.name}')

        # If no specific files found, copy all RTL files
        if not copied_files:
            print('  No specific module files found, copying all RTL files')
            for pattern in self.rtl.file_patterns:
                for src_file in self.rtl_dir.glob(pattern):
                    dst_file = work_dir / src_file.name
                    shutil.copy2(src_file, dst_file)
                    copied_files.append(str(dst_file))

        # Build output
        output = data.copy()
        set_field(output, 'critical_path_info.dir', str(work_dir))
        set_field(output, 'critical_path_info.module_names', list(modules_to_optimize))
        set_field(output, 'critical_path_info.critical_path.start', start_flop)
        set_field(output, 'critical_path_info.critical_path.end', end_flop)

        if synalign_mapping is not None:
            set_field(output, 'critical_modules.synalign_mapping', synalign_mapping)

        print(f'  Output directory: {work_dir}')
        print(f'  Files copied: {len(copied_files)}')

        return output

    def _locate_modules_and_launch_capture_flops(self) -> Tuple[List[str], str, str]:
        """
        Get the source module names that constitute the critical path.

        This method:
        1. Parses timing report to extract launch/capture flip-flop instances
        2. Extracts Q/D signal names from the synthesized netlist
        3. Invokes cli_locator to find signal locations in source Verilog files
        4. Extracts module names from the source Verilog files

        Returns:
            List of source module names and launch/capture flip-flop instances
        """
        # Read timing report to find launch (Q) and capture (D) flip-flops
        timing_text = self.report_path.read_text()

        # Pattern to match flip-flop instance references like: _105621_/Q (sky130_fd_sc_hd__dfrtp_1)
        # The cell type must contain "df" (delay flop, hardcoded for now) to verify it's actually a flip-flop
        launch_capture_pattern = re.compile(r'(_\d+_)/(Q|D)\s*\((.*?)\)')
        matches = launch_capture_pattern.findall(timing_text)

        launch = None
        capture = None
        for inst, pin, cell in matches:
            if 'df' not in cell.lower():
                continue
            if pin == 'Q' and launch is None:
                launch = (inst, cell)
            if pin == 'D' and capture is None:
                capture = (inst, cell)

        # Read netlist to extract Q signal names
        netlist_text = self.netlist_path.read_text()

        if launch is None:
            print('  Warning: Could not find launch flip-flops in timing report {self.report_path}')
        else:
            print(f'  Launch flop: {launch[0]} ({launch[1]})')
            try:
                launch_q_signal = self._extract_q_signal(netlist_text, launch[0])
                print(f'  Launch Q signal: {launch_q_signal}')
            except RuntimeError as e:
                print(f'  Warning: {e}')
        
        if capture is None:
            print('  Warning: Could not find capture flip-flops in timing report {self.report_path}')
        else:
            print(f'  Capture flop: {capture[0]} ({capture[1]})')
            try:
                # We also use `extract_q_signal` as the capture D signal is often a randomly named wire
                capture_d_signal = self._extract_q_signal(netlist_text, capture[0])
                print(f'  Capture D signal: {capture_d_signal}')
            except RuntimeError as e:
                print(f'  Warning: {e}')


        # Find source modules using cli_locator
        source_modules = []

        # Get hierarchy prefix from synth_top_module if available
        # Format: "output_module$hierarchy.path" → extract "hierarchy.path"
        hierarchy_prefix = self.benchmark.top_module
        synth_top = self.benchmark.synth_top_module
        if synth_top and '$' in synth_top:
            # Extract the part after '$' which is the full instance path
            hierarchy_prefix = synth_top.split('$', 1)[1]
            print(f'  Using hierarchy prefix from synth_top_module: {hierarchy_prefix}')

        for signal_name in [launch_q_signal, capture_d_signal]:
            # Construct full VCD hierarchical path
            vcd_path = f'{hierarchy_prefix}.{signal_name}'
            locations = self._invoke_locator(vcd_path)

            if not locations:
                print(f'  Warning: No locations found for {vcd_path}')
                continue

            # Extract source module from first location
            file_path, _ = locations[0]
            source_module = self._extract_module_name_from_file(file_path)

            if source_module and source_module not in source_modules:
                source_modules.append(source_module)
                print(f'  Found source module: {source_module}')

        return source_modules, launch_q_signal, capture_d_signal

    def _run_synalign(self, data: Dict, tools: ToolsConfig, critical_path_modules: List[str]) -> Optional[Dict]:
        """
        Run SynAlign to map all timing report nets back to original RTL source.

        Invokes scripts/run_synalign.py as a subprocess. Performs a sanity check
        comparing synalign's start/end flop modules with locator's results.

        Returns:
            Parsed synalign mapping dict, or None on failure.
        """
        if not tools.lgshell_path:
            print('  Warning: run_synalign enabled but lgshell_path not set, skipping')
            return None

        if not tools.liberty_file:
            print('  Warning: run_synalign enabled but liberty_file not set, skipping')
            return None

        # Find run_synalign.py script
        this_file = Path(__file__).resolve()
        hagent_root = this_file.parent.parent.parent.parent.parent
        synalign_script = hagent_root / 'scripts' / 'run_synalign.py'

        if not synalign_script.exists():
            print(f'  Warning: run_synalign.py not found at {synalign_script}')
            return None

        # Gather RTL source args
        standalone_files = None
        manifest_file = None
        if self.rtl.standalone_files:
            standalone_files = self.rtl.standalone_files
        if self.rtl.manifest_file:
            manifest_file = self.rtl.manifest_file

        synth_top = self.benchmark.effective_synth_top
        orig_top = self.benchmark.synth_top_module or synth_top
        elab_top = self.benchmark.top_module
        output_dir = str(Path(self.storage.output_dir) / 'synalign')
        os.makedirs(output_dir, exist_ok=True)

        # Build command
        cmd = [
            sys.executable, str(synalign_script),
            '--timing-report', str(self.report_path),
            '--netlist',
            str(self.netlist_path),
            '--liberty',
            tools.liberty_file,
            '--lgshell',
            tools.lgshell_path,
            '--synth-top',
            synth_top,
            '--orig-top',
            orig_top,
            '--elab-top',
            elab_top,
            '--output-dir',
            output_dir,
        ]

        if standalone_files:
            cmd.append('--standalone-files')
            cmd.extend(standalone_files)
        if manifest_file:
            cmd.extend(['--manifest-file', manifest_file])

        print(f'  Running synalign: {" ".join(cmd[:8])}...')

        try:
            result = subprocess.run(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                timeout=360,
            )
        except subprocess.TimeoutExpired:
            print('  Warning: synalign timed out after 360s')
            return None
        except Exception as e:
            print(f'  Warning: synalign failed: {e}')
            return None

        if result.stderr:
            for line in result.stderr.strip().splitlines():
                print(f'  [synalign] {line}')

        if result.returncode != 0:
            print(f'  Warning: synalign exited with code {result.returncode}')
            return None

        # Parse JSON output from stdout
        try:
            parsed = json.loads(result.stdout)
        except json.JSONDecodeError:
            print('  Warning: Could not parse synalign JSON output')
            return None

        mappings = parsed.get('mappings', [])
        print(f'  Synalign returned {len(mappings)} net mappings')

        # Sanity check: compare synalign module results with locator results
        if mappings and critical_path_modules:
            synalign_modules = sorted(set(m.get('orig_module', '') for m in mappings))
            synalign_modules = [m for m in synalign_modules if m]

            locator_set = set(critical_path_modules)
            synalign_set = set(synalign_modules)

            # Check if locator's start/end modules appear in synalign results
            missing = locator_set - synalign_set
            if missing:
                print(f'  Warning: Locator modules not found in synalign results: {missing}')
            else:
                print('  Sanity check passed: locator modules found in synalign mapping')

        return parsed

    def _extract_q_signal(self, netlist_text: str, instance_name: str) -> str:
        """Extract the Q signal name from a flip-flop instance in the netlist."""
        # Pattern to match flip-flop instantiation
        inst_pattern = re.compile(rf'sky130_fd_sc_hd__\w+\s+{re.escape(instance_name)}\s*\((.*?)\);', re.DOTALL)

        inst_match = inst_pattern.search(netlist_text)
        if not inst_match:
            raise RuntimeError(f'Instance {instance_name} not found in netlist')

        inst_block = inst_match.group(1)

        # Search for .Q(...) port connection
        q_pattern = re.compile(r'\.Q\s*\(\s*(.*?)\s*\)', re.DOTALL)
        q_match = q_pattern.search(inst_block)
        if not q_match:
            raise RuntimeError(f'.Q port not found for {instance_name}')

        raw_signal = q_match.group(1)
        # Cleanup: remove backslash, truncate at whitespace or '['
        cleaned = re.sub(r'\\?([^\s\[]+).*', r'\1', raw_signal).strip()
        return cleaned

    def _invoke_locator(self, vcd_signal_path: str) -> List[Tuple[str, int]]:
        """
        Invoke cli_locator.py to find the source location of a signal.

        Args:
            vcd_signal_path: Full VCD hierarchical path (e.g., "TopModule.signal_name")

        Returns:
            List of (file_path, line_number) tuples
        """
        # Find cli_locator.py
        this_file = Path(__file__).resolve()
        hagent_root = this_file.parent.parent.parent.parent.parent
        cli_locator_path = hagent_root / 'hagent' / 'inou' / 'cli_locator.py'

        if not cli_locator_path.exists():
            print(f'  Warning: cli_locator not found at {cli_locator_path}')
            return []

        # Locator command
        cmd = [
            sys.executable, str(cli_locator_path),
            '--api', 'locate_vcd',
            '--to', 'verilog',
        ]

        # Add config file and profile's name if specified
        if self.benchmark.hagent_profile_name:
            cmd.extend(['--name', self.benchmark.hagent_profile_name])
        if self.benchmark.hagent_config_yaml:
            cmd.extend(['--config', self.benchmark.hagent_config_yaml])

        cmd.append(vcd_signal_path)

        try:
            result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=60)

            if result.returncode != 0:
                return []

            # Parse output: format is "file_path:line_start-line_end"
            locations = []
            for line in result.stdout.strip().split('\n'):
                if not line:
                    continue
                match = re.match(r'^(.+):(\d+)-(\d+)', line)
                if match:
                    file_path = match.group(1)
                    line_start = int(match.group(2))
                    locations.append((file_path, line_start))

            return locations

        except Exception as e:
            print(f'  Warning: cli_locator failed: {e}')
            return []

    def _extract_module_name_from_file(self, file_path: str) -> Optional[str]:
        """Extract the module name from a Verilog source file."""
        try:
            content = Path(file_path).read_text()

            # Find module declaration
            module_pattern = re.compile(r'^\s*module\s+(\w+)\s*[#(]', re.MULTILINE)
            match = module_pattern.search(content)

            if match:
                return match.group(1)

            # Fallback: extract from filename
            return Path(file_path).stem

        except Exception:
            return None

    def _parse_module_hierarchy(self) -> Dict[str, List[str]]:
        """
        Parse module hierarchy using slang-hier command.

        Returns:
            Dictionary mapping parent module -> list of child modules it instantiates
        """
        # Build slang-hier command
        cmd = ['slang-hier', '--top', self.benchmark.top_module]

        # Add standalone files first
        if hasattr(self.rtl, 'standalone_files') and self.rtl.standalone_files:
            for f in self.rtl.standalone_files:
                cmd.append(f)

        # Add manifest file with -f flag
        if hasattr(self.rtl, 'manifest_file') and self.rtl.manifest_file:
            cmd.extend(['-f', self.rtl.manifest_file])

        print(f'  Running: {" ".join(cmd)}')

        try:
            result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=120)

            if result.returncode != 0:
                self.error(f'  Error: slang-hier failed: {result.stderr}')

            return self._parse_slang_hier_output(result.stdout)

        except Exception as e:
            self.error(f'  Warning: slang-hier error: {e}')

    def _parse_slang_hier_output(self, output: str) -> Dict[str, List[str]]:
        """
        Parse slang-hier output to build hierarchy dict.

        Output format:
            Module="frontend" Instance="cva6_nocache.i_frontend" File="..."
        """
        hierarchy: Dict[str, List[str]] = {}
        instance_to_module: Dict[str, str] = {}

        # Parse each line
        line_pattern = re.compile(r'Module="(\w+)"\s+Instance="([^"]+)"')
        for line in output.split('\n'):
            match = line_pattern.search(line)
            if not match:
                continue

            module_name = match.group(1)
            instance_path = match.group(2)
            instance_to_module[instance_path] = module_name

        # Build hierarchy: for each instance, find parent and add child
        for instance_path, module_name in instance_to_module.items():
            # Find parent instance by removing last component
            if '.' not in instance_path:
                # Top-level module, no parent
                if module_name not in hierarchy:
                    hierarchy[module_name] = []
                continue

            parent_instance = instance_path.rsplit('.', 1)[0]
            parent_module = instance_to_module.get(parent_instance)

            if parent_module:
                if parent_module not in hierarchy:
                    hierarchy[parent_module] = []
                if module_name not in hierarchy[parent_module]:
                    hierarchy[parent_module].append(module_name)

        return hierarchy

    def _build_parent_map(self, hierarchy: Dict[str, List[str]]) -> Dict[str, List[str]]:
        """Build reverse mapping: child -> list of parents that instantiate it."""
        parent_map = {}

        for parent, children in hierarchy.items():
            for child in children:
                if child not in parent_map:
                    parent_map[child] = []
                parent_map[child].append(parent)

        return parent_map

    def _find_path_to_root(self, module: str, parent_map: Dict[str, List[str]]) -> List[str]:
        """
        Find path from a module to the top module.

        Returns:
            List representing path from module to top (inclusive), or empty if no path
        """
        top_module = self.benchmark.top_module

        if module == top_module:
            return [top_module]

        if module not in parent_map:
            return []

        visited = set()
        path = [module]
        current = module

        while current != top_module:
            if current in visited:
                return []  # Cycle detected

            visited.add(current)

            if current not in parent_map or len(parent_map[current]) == 0:
                return []  # No path to top

            # Take first parent (assumes tree structure)
            parent = parent_map[current][0]
            path.append(parent)
            current = parent

        return path

    def _find_lca(self, modules: List[str], parent_map: Dict[str, List[str]]) -> Optional[str]:
        """
        Find the Lowest Common Ancestor (LCA) of a list of modules.

        Returns:
            LCA module name, or None if not found
        """
        top_module = self.benchmark.top_module

        if not modules or len(modules) == 1:
            return None

        # Find paths to root for all modules
        paths = []
        for module in modules:
            path = self._find_path_to_root(module, parent_map)
            if not path:
                return None
            paths.append(path)

        # Find LCA by checking common ancestors from top down
        min_path_len = min(len(p) for p in paths)
        lca_candidate = top_module

        for i in range(min_path_len):
            # Check ancestors at level i from the end (top)
            ancestors = [path[-(i + 1)] for path in paths]
            if len(set(ancestors)) == 1:
                lca_candidate = ancestors[0]
            else:
                break

        return lca_candidate

    def _collect_modules_to_optimize(
        self, critical_modules: List[str], hierarchy: Dict[str, List[str]]
    ) -> Tuple[List[str], Optional[str]]:
        """
        Collect all modules to optimize: critical modules + ancestors up to LCA.

        Returns:
            Tuple of (list of module names to optimize, LCA module name)
        """
        top_module = self.benchmark.top_module

        if not critical_modules:
            return [], None

        parent_map = self._build_parent_map(hierarchy)

        # Find LCA
        lca = self._find_lca(critical_modules, parent_map)

        if lca is None:
            return critical_modules, None

        # Collect all modules from critical modules up to LCA
        modules_to_optimize = set(critical_modules)

        if lca != top_module:
            modules_to_optimize.add(lca)

        for module in critical_modules:
            path = self._find_path_to_root(module, parent_map)
            for m in path:
                if m == top_module:
                    break
                modules_to_optimize.add(m)
                if m == lca:
                    break

        # Remove top module from optimization set
        modules_to_optimize.discard(top_module)

        return list(modules_to_optimize), lca

    def _map_modules_to_files(self) -> Dict[str, Path]:
        """Map module names to their RTL source files."""
        module_to_file = {}

        for pattern in self.rtl.file_patterns:
            for rtl_file in self.rtl_dir.rglob(pattern):
                try:
                    content = rtl_file.read_text()

                    # Find module declarations
                    for match in re.finditer(r'\bmodule\s+(\w+)', content):
                        module_name = match.group(1)
                        module_to_file[module_name] = rtl_file

                except Exception:
                    continue

        return module_to_file


if __name__ == '__main__':
    step = ExtractCriticalStep()
    step.parse_arguments()
    step.setup()
    step.step()
