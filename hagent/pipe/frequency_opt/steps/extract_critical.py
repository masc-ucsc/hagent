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
from hagent.inou.locator import Locator, RepresentationType
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
        self.locator: Optional[Locator] = None

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

        # Initialize Locator for signal location and hierarchy queries
        self.locator = Locator(
            config_path=self.benchmark.hagent_config_yaml,
            profile_name=self.benchmark.hagent_profile_name,
        )
        if not self.locator.setup():
            self.error(f'Locator setup failed: {self.locator.get_error()}')

        # Step 1: Extract critical path module names from timing report
        critical_path_modules, start_flop, end_flop = self._locate_modules_and_launch_capture_flops()
        print(f'  Critical path modules: {critical_path_modules}')

        # Optional: Run synalign for full net mapping
        tools = ToolsConfig.from_data_optional(data, 'tools')
        synalign_mapping = None
        if tools and tools.run_synalign:
            synalign_mapping = self._run_synalign(data, tools, critical_path_modules)

        # Step 2-5: Determine modules to optimize and copy RTL files
        work_dir = Path(self.storage.output_dir) / 'critical_modules'
        if os.path.exists(work_dir):
            shutil.rmtree(work_dir)
            print('  Removed existing critical modules dir')
        os.makedirs(work_dir)
            
        hierarchy = self._get_hierarchy_from_locator()

        if synalign_mapping is not None:
            # Synalign provides file_path directly — extract unique files and module names
            synalign_files = sorted(set(
                m['file_path'] for m in synalign_mapping.get('mappings', [])
                if m.get('file_path')
            ))

            # Filter: only include files whose module (stem) exists in the hierarchy.
            # This excludes packages and other non-module files that synalign may annotate.
            hierarchy_modules = set(hierarchy.keys())
            for children in hierarchy.values():
                hierarchy_modules.update(children)

            modules_to_optimize = []
            copied_files = []
            for fpath in synalign_files:
                src_path = Path(fpath)
                if not src_path.exists():
                    continue
                # Important (maybe fragile) assumption: all files module names matched their path stem's name
                module_name = src_path.stem
                if module_name not in hierarchy_modules:
                    print(f'  Skipping {src_path.name} (not a module in hierarchy, likely a package)')
                    continue
                dst_file = work_dir / src_path.name
                shutil.copy2(src_path, dst_file)
                copied_files.append(str(dst_file))
                modules_to_optimize.append(module_name)
                print(f'  Copied: {src_path.name}')
            lca = None
            print(f'  Using synalign modules: {modules_to_optimize}')
        else:
            # No synalign — use locator + LCA as before
            print(f'  Found {len(hierarchy)} modules in hierarchy')
            modules_to_optimize, lca = self._collect_modules_to_optimize(critical_path_modules, hierarchy)

            module_to_file = self._map_modules_to_files()
            copied_files = []
            for module_name in modules_to_optimize:
                if module_name in module_to_file:
                    src_file = module_to_file[module_name]
                    dst_file = work_dir / src_file.name
                    shutil.copy2(src_file, dst_file)
                    copied_files.append(str(dst_file))
                    print(f'  Copied: {src_file.name}')

        print(f'  LCA: {lca}')
        print(f'  Modules to optimize: {modules_to_optimize}')

        if not copied_files:
            self.error('  No module files across critical path')

        # Build output
        output = data.copy()
        set_field(output, 'critical_path_info.dir', str(work_dir))
        set_field(output, 'critical_path_info.module_names', list(modules_to_optimize))
        set_field(output, 'critical_path_info.critical_path.start', start_flop)
        set_field(output, 'critical_path_info.critical_path.end', end_flop)

        if synalign_mapping is not None:
            commented_dir = self._annotate_rtl_with_critical_comments(synalign_mapping)
            if commented_dir:
                set_field(output, 'critical_path_info.commented_rtl_dir', str(commented_dir))

        print(f'  Output directory: {work_dir}')
        print(f'  Files copied: {len(copied_files)}')

        # Cleanup Locator resources
        if self.locator:
            self.locator.cleanup()
            self.locator = None

        return output

    def _locate_modules_and_launch_capture_flops(self) -> Tuple[List[str], str, str]:
        """
        Get the source module names that constitute the critical path.

        This method:
        1. Parses timing report to extract launch/capture flip-flop instances
        2. Extracts Q/D signal names from the synthesized netlist
        3. Uses Locator to find signal locations in source Verilog files

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

        launch_q_signal = ''
        capture_d_signal = ''

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

        # Find source modules using Locator directly
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
            if not signal_name:
                continue
            # Construct full VCD hierarchical path
            vcd_path = f'{hierarchy_prefix}.{signal_name}'
            locations = self.locator.locate_vcd(to=RepresentationType.VERILOG, vcd_variable=vcd_path)

            if not locations:
                print(f'  Warning: No locations found for {vcd_path}')
                continue

            # SourceLocation has module_name from hierarchy
            source_module = locations[0].module_name
            if not source_module:
                source_module = Path(locations[0].file_path).stem

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

        # Gather RTL source args for LiveHD inou.yosys
        standalone_files = None
        manifest_file = None
        if self.rtl.standalone_files:
            standalone_files = self.rtl.standalone_files
        if self.rtl.manifest_file:
            manifest_file = self.rtl.manifest_file

        synth_top = self.benchmark.effective_output_module
        orig_top = self.benchmark.synth_top_module or synth_top
        if '\\$' in orig_top:
            orig_top = orig_top.replace('\\$', '$')
        elab_top = self.benchmark.top_module
        output_dir = str(Path(self.storage.output_dir) / 'synalign')
        os.makedirs(output_dir, exist_ok=True)

        # Build command
        cmd = [
            sys.executable, str(synalign_script),
            '--timing-report', str(self.report_path),
            '--netlist', str(self.netlist_path),
            '--liberty', tools.liberty_file,
            '--lgshell', tools.lgshell_path,
            '--synth-top', synth_top,
            '--orig-top', orig_top,
            '--elab-top', elab_top,
            '--output-dir', output_dir,
        ]

        if standalone_files:
            cmd.append('--standalone-files')
            cmd.extend(standalone_files)
        if manifest_file:
            cmd.extend(['--manifest-file', manifest_file])

        print(f'  Running synalign: {" ".join(cmd)}')

        try:
            result = subprocess.run(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                timeout=1200,
            )
        except subprocess.TimeoutExpired:
            print('  Warning: synalign timed out after 1200s')
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

        # Sanity check: read synalign file_paths and grep for module declarations
        if mappings and critical_path_modules:
            synalign_files = sorted(set(
                m['file_path'] for m in mappings if m.get('file_path')
            ))
            # Collect all module names declared in synalign's files
            module_decl_re = re.compile(r'^\s*module\s+(\w+)', re.MULTILINE)
            synalign_declared_modules: set = set()
            for fpath in synalign_files:
                p = Path(fpath)
                if p.exists():
                    content = p.read_text()
                    synalign_declared_modules.update(module_decl_re.findall(content))

            locator_set = set(critical_path_modules)
            missing = locator_set - synalign_declared_modules
            if missing:
                print(f'  Warning: Locator modules not found in synalign files: {missing}')
            else:
                print('  Sanity check passed: locator modules found in synalign files')

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

    def _get_hierarchy_from_locator(self) -> Dict[str, List[str]]:
        """
        Get module hierarchy from Locator's cached slang-hier result.

        Converts the Locator's instance-based hierarchy into a parent->children
        module mapping needed for LCA computation.

        Returns:
            A mapping from parent module to list of child modules it instantiates
        """
        instance_hierarchy = self.locator.get_hierarchy()

        # Build instance_path → module_name mapping from Locator's format
        instance_to_module: Dict[str, str] = {}
        for inst_path, info in instance_hierarchy.items():
            if inst_path == '_metadata':
                continue
            instance_to_module[inst_path] = info.get('module', '')

        # Convert to parent module -> child modules mapping
        hierarchy: Dict[str, List[str]] = {}
        for instance_path, module_name in instance_to_module.items():
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
        if not critical_modules:
            return [], None

        parent_map = self._build_parent_map(hierarchy)

        # Find LCA
        lca = self._find_lca(critical_modules, parent_map)

        if lca is None:
            return critical_modules, None

        # Collect all modules from critical modules up to LCA
        top_module = self.benchmark.top_module
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
        """Map module names to their RTL source files (absolute path) using Locator's hierarchy.

        slang-hier already outputs Module to  File mappings, so we extract them
        directly from the cached hierarchy instead of re-scanning RTL files.
        """
        instance_hierarchy = self.locator.get_hierarchy()
        metadata = instance_hierarchy.get('_metadata', {})
        hier_cwd = metadata.get('cwd', '')

        # Resolve base directory for relative file paths from slang-hier
        from hagent.inou.path_manager import PathManager

        pm = PathManager()
        base_dir = Path(hier_cwd.replace('$HAGENT_BUILD_DIR', str(pm.build_dir)).replace('$HAGENT_REPO_DIR', str(pm.repo_dir)))

        module_to_file: Dict[str, Path] = {}
        for inst_path, info in instance_hierarchy.items():
            if inst_path == '_metadata':
                continue
            module_name = info.get('module', '')
            file_path = info.get('file', '')
            if module_name and file_path and module_name not in module_to_file:
                resolved = base_dir / file_path if not Path(file_path).is_absolute() else Path(file_path)
                module_to_file[module_name] = resolved

        return module_to_file

    def _extract_signal_name(self, orig_info: str) -> Optional[str]:
        """Extract signal name from synalign orig_info field.

        Format: "n1044,lu_hit_o(mux,,cva6_tlb$cva6_nocache.ex_stage_i...)"
        Returns: "lu_hit_o", or None if not parseable or is a pin-number (p0, p1, ...).
        """
        match = re.match(r'n\d+,(\w+)\(', orig_info)
        if not match:
            return None
        name = match.group(1)
        # For those pin-number names (like p0, p1) produced by LiveHD,
        # we don't provide specific signal names in the annotation
        if re.fullmatch(r'p\d+', name) or name == "empty":
            return ""
        return name

    def _annotate_rtl_with_critical_comments(self, synalign_result: Dict) -> Optional[Path]:
        """Annotate RTL source files with CRITICAL comments from synalign mapping.

        Copies affected RTL files to <output_dir>/commented_rtl/ and inserts
        '// CRITICAL: signal1, signal2, ...' comments at the lines identified
        by synalign. Never modifies the original source files.

        Args:
            synalign_result: Parsed output from run_synalign.py containing 'mappings' list.

        Returns:
            Path to commented_rtl directory, or None if no annotations were made.
        """
        mappings = synalign_result.get('mappings', [])
        if not mappings:
            return None

        # Group signal names by (file_path, line_number)
        # key: (abs_file_path, line_no) → set of signal names
        annotations: Dict[Tuple[str, int], set] = {}
        for entry in mappings:
            file_path = entry.get('file_path')
            line_no = entry.get('line')
            orig_info = entry.get('orig_info', '')
            if not file_path or not line_no:
                continue

            signal = self._extract_signal_name(orig_info)
            if signal is None:
                continue

            key = (file_path, line_no)
            if key not in annotations:
                annotations[key] = set()
            annotations[key].add(signal)

        if not annotations:
            print('  No valid annotations from synalign')
            return None

        # Group annotations by file
        file_annotations: Dict[str, Dict[int, set]] = {}
        for (fpath, line_no), signals in annotations.items():
            if fpath not in file_annotations:
                file_annotations[fpath] = {}
            file_annotations[fpath][line_no] = signals

        # Create commented_rtl directory
        commented_dir = Path(self.storage.output_dir) / 'commented_rtl'
        if commented_dir.exists():
            shutil.rmtree(commented_dir)
        os.makedirs(commented_dir)

        annotated_count = 0
        for src_file_path, line_signals in file_annotations.items():
            src_path = Path(src_file_path)
            if not src_path.exists():
                self.error(f'  Error: Source file not found for annotation: {src_path}')

            lines = src_path.read_text().splitlines(keepends=True)
            dst_path = commented_dir / src_path.name

            # Build annotated content: insert CRITICAL comment before each target line
            new_lines = []
            for i, line in enumerate(lines, 1):
                if i in line_signals:
                    signal_list = ', '.join(sorted(line_signals[i]))
                    # Detect indentation from the target line
                    indent = re.match(r'^(\s*)', line).group(1)
                    new_lines.append(f'{indent}// CRITICAL: {signal_list}\n')
                new_lines.append(line)

            dst_path.write_text(''.join(new_lines))
            annotated_count += 1
            print(f'  Annotated: {src_path.name} ({len(line_signals)} locations)')

        print(f'  Commented RTL directory: {commented_dir} ({annotated_count} files)')
        return commented_dir

    def _build_llm_optimization_prompt(
        self,
        synalign_result: Dict,
        commented_rtl_dir: Path,
    ) -> str:
        """Build a structured LLM prompt for critical path optimization.

        Combines STA report timing data with synalign net-to-signal mapping to
        produce a prompt that tells the LLM exactly which signals are on the
        critical path, their delays, fanout, and source locations.

        Args:
            synalign_result: Parsed synalign output with 'mappings' list.
            commented_rtl_dir: Path to the annotated RTL directory.

        Returns:
            Formatted prompt string for the LLM.
        """
        # TODO: Parse STA report to extract per-net delay and fanout
        #   - Pattern for net lines: r'^\s*(\d+)\s+[\d.]+\s+[\d.]+\s+[\d.]+\s+.*$' (fanout line)
        #   - Pattern for net name: r'^\s+(\S+)\s+\(net\)' (net name line follows)
        #   - Build dict: net_name → {fanout, delay, arrival_time}

        # TODO: Build synth_instance → signal mapping from synalign
        #   - Map each synth_instance (e.g. "_015978_") to signal name + file + line
        #   - Use _extract_signal_name() for name extraction

        # TODO: Traverse STA critical path nets in order, look up each in synalign mapping
        #   - For each net, emit: "Signal: <name> in <file>:<line> | delay: <ns> | fanout: <N>"

        # TODO: Assemble the final prompt:
        #   I am optimizing the timing frequency of {top_module}.
        #
        #   The Critical Path flows through these RTL points:
        #   [ordered list of signals with delay/fanout info]
        #
        #   The RTL source code directory is in: {commented_rtl_dir}
        #
        #   Task:
        #   1. Analyze the logic of this critical path using the signal names and relations,
        #      figure out the bottlenecks.
        #   2. Optimize the modules without introducing new pipeline stages
        #      (e.g., restructure mux trees, use parallel cases, move critical wires out of
        #      nested if-else, use optimized arithmetic like carry-lookahead adders).
        #   3. Make sure the optimization does not break logical equivalence check.
        #   4. Provide the optimized RTL code.

        return f'TODO: LLM optimization prompt for {self.benchmark.top_module}'


if __name__ == '__main__':
    step = ExtractCriticalStep()
    step.parse_arguments()
    step.setup()
    step.step()
