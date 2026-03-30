# See LICENSE for details
"""
Extract Critical Path step: identifies RTL modules on the critical path.

This step analyzes the timing report to find which modules contribute
to the critical path, then uses LCA (Lowest Common Ancestor) to determine
which modules should be optimized.
"""

import os
import re
import shutil
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from hagent.core.step import Step
from hagent.inou.locator import Locator, RepresentationType
from hagent.tool.compile_slang import Compile_slang
from hagent.workflow.frequency_opt.common_utils import get_clock_signal
from hagent.workflow.frequency_opt.config import (
    DesignConfig,
    RTLConfig,
    StorageConfig,
    get_field,
    set_field,
)


class ExtractCriticalStep(Step):
    """
    Extract modules that traverses through the critical path.

    Required YAML sections:
      - design: top_module
      - rtl: source_dir
      - storage: output_dir

    Required YAML fields (from previous steps):
      - logs.sta_log
      - synthesis.netlist_path

    Writes to YAML:
      - critical_path_info.dir: Directory containing copied RTL files
      - critical_path_info.module_names: List of module names to optimize
      - critical_path_info.critical_path: Info for critical path,such as start/end flops
    """

    def __init__(self):
        super().__init__()

    def setup(self):
        super().setup()
        # Instance fields to store configuration - accessible by all helper methods
        data = self.input_data
        assert data is not None
        self.design = DesignConfig.from_data(data, 'design_info')
        self.rtl = RTLConfig.from_data(data, 'rtl')
        self.storage = StorageConfig.from_data(data, 'storage')
        assert self.rtl.netlist_file is not None
        self.netlist_path = Path(self.rtl.netlist_file)
        if not self.netlist_path.exists():
            self.error(f'Netlist not found: {self.netlist_path}')
        self.sta_report_path = Path(get_field(data, 'logs.sta_log'))
        if not self.sta_report_path.exists():
            self.error(f'Timing report not found: {self.sta_report_path}')
        # Initialize Locator for signal location and hierarchy queries
        self.locator = Locator(
            config_path=self.design.hagent_config_yaml,
            profile_name=self.design.hagent_profile_name,
        )
        if not self.locator.setup():
            self.error(f'Locator setup failed: {self.locator.get_error()}')

    def run(self, data: Dict) -> Dict:
        print('Extracting critical path modules:')
        print(f'  Timing report: {self.sta_report_path}')
        print(f'  Netlist: {self.netlist_path}')
        print(f'  RTL source: {self.rtl.source_dir}')

        # Invalidate Locator's outdated cache
        self.locator.invalidate_cache(force=True)

        # Extract critical path module names from timing report
        critical_path_modules, start_flop, end_flop = self._locate_modules_and_launch_capture_flops(
            self.sta_report_path, self.netlist_path
        )
        print(f'  Critical path modules: {critical_path_modules}')

        hierarchy = self._get_hierarchy_from_locator()

        # No synalign — use locator + LCA as before
        print(f'  Found {len(hierarchy)} modules in hierarchy')
        modules_to_optimize, lca = self._collect_modules_to_optimize(critical_path_modules, hierarchy)

        print(f'  LCA: {lca}')
        print(f'  Modules to optimize: {modules_to_optimize}')

        # Copy any module files not already in annotated_rtl
        annotated_dir = Path(self.storage.output_dir) / 'annotated_rtl'
        module_to_file = self._map_modules_to_files()
        for module_name in modules_to_optimize:
            if module_name in module_to_file:
                src_file = module_to_file[module_name]
                dst_file = annotated_dir / src_file.name
                if not dst_file.exists():
                    shutil.copy2(src_file, dst_file)
                    print(f'  Copied: {src_file.name}')

        # Build output
        output = data.copy()
        set_field(output, 'critical_path_info.dir', str(annotated_dir))
        set_field(output, 'critical_path_info.module_names', list(modules_to_optimize))
        set_field(output, 'critical_path_info.critical_path.start', start_flop)
        set_field(output, 'critical_path_info.critical_path.end', end_flop)

        print(f'  Output directory: {annotated_dir}')

        self.locator.cleanup()

        return output

    def _locate_external_input_port_flop(self, sta_report_path: Path, clock_signal: str) -> Optional[str]:
        """Try to find an external input port as the launch point from the timing report.

        Returns:
            The base port name if found, or None.
        """
        # matches the next line after "input external delay"
        # group(1) = full token e.g. input_data_i[132]
        input_ext_delay_nextline_re = re.compile(
            r'(?m)^[^\n]*\binput\s+external\s+delay\s*$\n'  # marker line
            r'^\s*[\d.]+\s+[\d.]+\s+[\d.]+\s+[v^]\s+([^\s(]+)'  # next line, capture "signal token"
        )

        def base_port_name(token: str) -> str:
            # input_data_i[132] -> input_data_i
            return re.sub(r'\[\d+\]$', '', token)

        try:
            content = sta_report_path.read_text()
            sections = re.split(r'(?=Startpoint:)', content)

            for section in sections:
                if not section.strip():
                    continue
                path_group_match = re.search(r'Path Group:\s*\**(\S+)\**', section)
                if not path_group_match or path_group_match.group(1) != clock_signal:
                    continue
                input_ext_delay_match = input_ext_delay_nextline_re.search(section)
                if input_ext_delay_match:
                    port_name = input_ext_delay_match.group(1)
                    return base_port_name(port_name)
        except Exception as e:
            print(f'    Warning: Failed to parse timing log: {e}')

        return None

    def _locate_modules_and_launch_capture_flops(self, sta_report_path: Path, netlist_path: Path) -> Tuple[List[str], str, str]:
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
        timing_text = sta_report_path.read_text()

        # Pattern to match flip-flop instance references like: _105621_/Q (sky130_fd_sc_hd__dfrtp_1)
        # The cell type must contain "df" (delay flop, hardcoded for now) to verify it's actually a flip-flop
        clock_signal = get_clock_signal(netlist_path)
        assert clock_signal is not None

        q_d_pattern = re.compile(r'(_\d+_)/(Q|D)\s*\((.*?)\)')
        matches = q_d_pattern.findall(timing_text)

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
        netlist_text = netlist_path.read_text()

        launch_q_signal = ''
        launch_src_file: Optional[Path] = None
        capture_d_signal = ''
        capture_src_file: Optional[Path] = None

        # Fresh annotated_rtl directory for this invocation
        annotated_dir = Path(self.storage.output_dir) / 'annotated_rtl'
        if annotated_dir.exists():
            shutil.rmtree(annotated_dir)
        annotated_dir.mkdir(parents=True)

        # Track annotation insertions per file: filename -> list of original 0-indexed lines
        self._annotation_offsets: Dict[str, List[int]] = {}

        # Launch: try Q flop first, then fall back to external input port
        if launch is not None:
            print(f'  Launch flop: {launch[0]} ({launch[1]})', end='')
            try:
                launch_q_signal, launch_src_file, launch_src_line = self._extract_q_signal(netlist_text, launch[0])
                print(f'  Launch Q signal: {launch_q_signal}')
                if launch_src_file and launch_src_line is not None:
                    print(f'  Launch source: {launch_src_file} line {launch_src_line}')
                self._annotate_instance_module(
                    launch_q_signal,
                    'the starting flop of the critical path',
                    src_line=launch_src_line,
                )
            except RuntimeError as e:
                print(f'\n  Warning: {e}')

        if not launch_q_signal:
            ext_port = self._locate_external_input_port_flop(sta_report_path, clock_signal)
            if ext_port:
                launch_q_signal = ext_port
                print(f'  Launch from external input port: {launch_q_signal}', end='')
                self._annotate_module_port(
                    self.design.effective_output_module,
                    ext_port,
                    'the starting external input port of the critical path',
                )
            else:
                print(f'  Warning: Could not find launch flip-flops in timing report {sta_report_path}')

        # Capture: try D flop first (external output port not implemented yet)
        if capture is not None:
            print(f'  Capture flop: {capture[0]} ({capture[1]})', end='')
            try:
                # We also use `extract_q_signal` as the capture D signal is often a randomly named wire
                capture_d_signal, capture_src_file, capture_src_line = self._extract_q_signal(netlist_text, capture[0])
                print(f'  Capture D signal: {capture_d_signal}')
                if capture_src_file and capture_src_line is not None:
                    print(f'  Capture source: {capture_src_file} line {capture_src_line}')
                self._annotate_instance_module(
                    capture_d_signal,
                    'the ending flop of the critical path',
                    src_line=capture_src_line,
                )
            except RuntimeError as e:
                print(f'\n  Warning: {e}')

        if not capture_d_signal:
            print(f'  Warning: Could not find capture flip-flops in timing report {sta_report_path}')

        # Find source modules using Locator directly
        source_modules = []

        # Get hierarchy prefix from synth_top_module if available
        # Format: "output_module$hierarchy.path" → extract "hierarchy.path"
        hierarchy_prefix = self.design.top_module
        synth_top = self.design.synth_top_module
        if synth_top and '$' in synth_top:
            # Extract the part after '$' which is the full instance path
            hierarchy_prefix = synth_top.split('$', 1)[1]
            print(f'  Using hierarchy prefix from synth_top_module: {hierarchy_prefix}')

        # Map signal_name -> src_file for fallback module discovery
        signal_src_files = {}
        if launch_q_signal and launch_src_file:
            signal_src_files[launch_q_signal] = launch_src_file
        if capture_d_signal and capture_src_file:
            signal_src_files[capture_d_signal] = capture_src_file

        module_to_file = self._map_modules_to_files()
        # Reverse map: filename -> module name
        file_to_module = {p.name: m for m, p in module_to_file.items()}

        for signal_name in [launch_q_signal, capture_d_signal]:
            if not signal_name:
                continue
            # Construct full VCD hierarchical path
            vcd_path = f'{hierarchy_prefix}.{signal_name}'
            locations = self.locator.locate_vcd(to=RepresentationType.VERILOG, vcd_variable=vcd_path)

            if locations:
                # SourceLocation has module_name from hierarchy
                source_module = locations[0].module_name
                if not source_module:
                    source_module = Path(locations[0].file_path).stem
            else:
                # Fallback: derive module from (* src *) file when VCD lookup fails
                # (e.g. signal is a synthesized name like _20608_)
                src_file = signal_src_files.get(signal_name)
                if src_file:
                    source_module = file_to_module.get(src_file.name, src_file.stem)
                    print(f'  Derived module from (* src *): {source_module} ({src_file.name})')
                else:
                    print(f'  Warning: No locations found for {vcd_path}')
                    continue

            if source_module and source_module not in source_modules:
                source_modules.append(source_module)
                print(f'  Found source module: {source_module}')

        return source_modules, launch_q_signal, capture_d_signal

    def _annotate_module_port(self, module_name: str, port_name: str, comment: str):
        """Annotate an external input/output port declaration using Compile_slang.

        Uses pyslang to find the exact declaration line of the port in the module,
        then inserts a CRITICAL comment before that line in annotated_rtl/.
        """
        module_to_file = self._map_modules_to_files()
        module_path = module_to_file.get(module_name)
        if not module_path:
            print(f'\n  Warning: No file found for module {module_name}')
            return

        if not module_path.exists():
            print(f'\n  Warning: Module file not found: {module_path}')
            return

        # Use Compile_slang to find the port declaration line
        compiler = Compile_slang()
        if not compiler.setup():
            print(f'\n  Warning: Compile_slang setup failed: {compiler.error_message}')
            return
        if not compiler.add_file(str(module_path)):
            print(f'\n  Warning: Compile_slang add_file failed: {compiler.error_message}')
            return

        ios = compiler.get_ios(module_name)
        target_line = None
        for io in ios:
            if io.name == port_name:
                target_line = io.line
                break

        if target_line is None or target_line == 0:
            print(f'\n  Warning: Port {port_name} not found by Compile_slang in {module_path.name}')
            return

        print(f' declaration line {target_line}')
        target_0 = target_line - 1  # convert 1-indexed to 0-indexed

        annotated_dir = Path(self.storage.output_dir) / 'annotated_rtl'
        annotated_dir.mkdir(parents=True, exist_ok=True)

        dst_path = annotated_dir / module_path.name
        source = dst_path if dst_path.exists() else module_path
        out_lines = source.read_text().splitlines(keepends=True)

        # Compute exact insertion point using tracked offsets from prior annotations
        prior = self._annotation_offsets.get(module_path.name, [])
        offset = sum(1 for p in prior if p <= target_0)
        target_idx = target_0 + offset

        if target_idx >= len(out_lines):
            print(f'\n  Warning: target line {target_line} out of range in {module_path.name}')
            return

        m = re.match(r'^(\s*)', out_lines[target_idx])
        indent = m.group(1) if m else ''
        annotation = f'{indent}// CRITICAL: {port_name} is {comment}\n'
        out_lines.insert(target_idx, annotation)
        dst_path.write_text(''.join(out_lines))
        self._annotation_offsets.setdefault(module_path.name, []).append(target_0)
        print(f'  Annotated {dst_path} — {port_name} is {comment}')

    def _resolve_instance_signal(self, signal_name: str) -> Tuple[Optional[str], str, Optional[Path]]:
        """Resolve a hierarchical signal into instance key, leaf signal, and module file.

        Uses the hierarchy prefix from effective_synth_top and the hierarchy dict
        to find the deepest matching instance path.

        Algorithm:
          1. Build full_path = hierarchy_prefix + "." + signal_name
          2. Try progressively shorter prefixes against hierarchy keys
          3. Fall back to suffix matching if no exact prefix match

        Returns:
            (hierarchy_key, leaf_signal_name, module_file_path)
            or (None, signal_name, None) on failure.
        """
        hierarchy = self.locator.get_hierarchy()

        # Get hierarchy prefix from effective_synth_top
        synth_top = self.design.effective_synth_top
        if '$' in synth_top:
            prefix = synth_top.split('$', 1)[1]
        else:
            prefix = synth_top

        full_path = f'{prefix}.{signal_name}'
        segments = full_path.split('.')

        # Try progressively shorter prefixes (deepest instance first)
        for i in range(len(segments) - 1, 0, -1):
            candidate = '.'.join(segments[:i])
            if candidate in hierarchy:
                leaf = '.'.join(segments[i:])
                info = hierarchy[candidate]
                file_path = info.get('file')
                return candidate, leaf, Path(file_path) if file_path else None

        # Fallback: suffix matching (for cases where prefix doesn't align with hierarchy keys)
        if '.' in signal_name:
            instance_suffix, leaf = signal_name.rsplit('.', 1)
            for inst_path, info in hierarchy.items():
                if inst_path.startswith('_'):
                    continue
                if inst_path == instance_suffix or inst_path.endswith('.' + instance_suffix):
                    file_path = info.get('file')
                    return inst_path, leaf, Path(file_path) if file_path else None

        return None, signal_name, None

    def _annotate_instance_module(self, signal_name: str, comment: str, src_line: Optional[int] = None):
        """Find the module file for a hierarchical signal and annotate it in annotated_rtl/.

        Uses _resolve_instance_signal to find the deepest matching instance in the
        hierarchy, then annotates the leaf signal in that module's source file.

        When src_line (1-indexed, from netlist (* src *)) is provided, targets that
        exact line instead of regex-searching for the first appearance.
        """
        if '.' not in signal_name:
            print(f'  Warning: Signal {signal_name} has no hierarchy, skipping annotation')
            return

        inst_key, leaf_signal, module_path = self._resolve_instance_signal(signal_name)

        if not inst_key or not module_path:
            print(f'  Warning: Instance for {signal_name} not found in hierarchy')
            return

        if not module_path.exists():
            print(f'  Warning: Module file not found: {module_path}')
            return

        # Use the final segment as the signal name to search for in the file
        port_name = leaf_signal.split('.')[-1] if '.' in leaf_signal else leaf_signal

        port_pattern = re.compile(rf'\b{re.escape(port_name)}\b')

        annotated_dir = Path(self.storage.output_dir) / 'annotated_rtl'
        annotated_dir.mkdir(parents=True, exist_ok=True)

        dst_path = annotated_dir / module_path.name
        # Read from annotated copy if it exists (to preserve earlier annotations)
        source = dst_path if dst_path.exists() else module_path
        out_lines = source.read_text().splitlines(keepends=True)

        if src_line is not None and src_line > 0:
            # Compute exact insertion point using tracked offsets from prior annotations
            target_0 = src_line - 1  # convert 1-indexed to 0-indexed
            prior = self._annotation_offsets.get(module_path.name, [])
            offset = sum(1 for p in prior if p <= target_0)
            target_idx = target_0 + offset

            if target_idx >= len(out_lines):
                print(f'  Warning: target line {src_line} out of range in {module_path.name}')
                return
        else:
            # Fallback: full-file regex search when src_line is unavailable
            target_idx = None
            for i, line in enumerate(out_lines):
                if port_pattern.search(line):
                    target_idx = i
                    break
            if target_idx is None:
                print(f'  Warning: Signal {port_name} not found in {module_path.name}')
                return
            target_0 = target_idx  # record actual index as the original line

        m = re.match(r'^(\s*)', out_lines[target_idx])
        indent = m.group(1) if m else ''
        annotation = f'{indent}// CRITICAL: {port_name} is {comment}\n'
        out_lines.insert(target_idx, annotation)
        dst_path.write_text(''.join(out_lines))
        self._annotation_offsets.setdefault(module_path.name, []).append(target_0)
        print(f'  Annotated {dst_path} — {port_name} is {comment}')

    def _extract_q_signal(self, netlist_text: str, instance_name: str) -> Tuple[str, Optional[Path], Optional[int]]:
        """Extract the Q signal name and source location from a flip-flop instance in the netlist.

        Looks at the line immediately before the instance for a (* src = "..." *)
        annotation and resolves the relative path against the netlist directory.

        Returns:
            Tuple of (signal_name, resolved_src_file, src_line_number).
            resolved_src_file and src_line_number are None if (* src = "..." *) not found.
        """
        # Pattern to match flip-flop instantiation
        inst_pattern = re.compile(rf'sky130_fd_sc_hd__\w+\s+{re.escape(instance_name)}\s*\((.*?)\);', re.DOTALL)

        inst_match = inst_pattern.search(netlist_text)
        if not inst_match:
            raise RuntimeError(f'Instance {instance_name} not found in netlist')

        # Try to extract source location from the line before the instance
        src_file = None
        src_line = None
        line_number = netlist_text[: inst_match.start()].count('\n') + 1
        print(f' netlist line {line_number}')
        lines = netlist_text.splitlines()
        if line_number >= 2:
            prev_line = lines[line_number - 2]  # one line before (0-indexed)
            src_match = re.search(r'\(\*\s*src\s*=\s*"([^"]+)"\s*\*\)', prev_line)
            if src_match:
                src_value = src_match.group(1)  # e.g. "/path/to/StageReg.sv:42.3"
                parts = src_value.rsplit(':', 1)
                if len(parts) == 2:
                    src_file = Path(parts[0])
                    assert src_file.is_absolute(), f'Expected absolute path in (* src *), got: {src_file}'
                    src_line = int(parts[1].split('.')[0])
            else:
                print(f'  Warning: No (* src = "..." *) found before instance {instance_name}')
        else:
            print(f'  Warning: No line before instance {instance_name} to check for (* src = "..." *)')

        inst_block = inst_match.group(1)

        # Search for .Q(...) port connection
        q_pattern = re.compile(r'\.Q\s*\(\s*(.*?)\s*\)', re.DOTALL)
        q_match = q_pattern.search(inst_block)
        if not q_match:
            raise RuntimeError(f'.Q port not found for {instance_name}')

        raw_signal = q_match.group(1)
        # Cleanup: strip leading backslash and trailing bus index only.
        # Intermediate [N] in instance names (e.g. g_blocks[0]) are preserved.
        # eg '\\pipeA_ex_mem.reg_nextpc [63]' -> 'pipeA_ex_mem.reg_nextpc'
        # eg '\\g_blocks[0].fpu.ctrl.sig [100]' -> 'g_blocks[0].fpu.ctrl.sig'
        stripped = raw_signal.lstrip('\\').strip()
        cleaned = re.sub(r'\s*\[\d+\]\s*$', '', stripped)
        return cleaned, src_file, src_line

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
            if inst_path == '_metadata' or inst_path == '_top_modules':
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
        top_module = self.design.top_module

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
        top_module = self.design.top_module

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
        top_module = self.design.top_module
        modules_to_optimize = set(critical_modules)

        modules_to_optimize.add(lca)

        for module in critical_modules:
            path = self._find_path_to_root(module, parent_map)
            for m in path:
                if m == top_module:
                    break
                modules_to_optimize.add(m)
                if m == lca:
                    break

        return list(modules_to_optimize), lca

    def _map_modules_to_files(self) -> Dict[str, Path]:
        """Map module names to their RTL source files (absolute path) using Locator's hierarchy.

        slang-hier already outputs Module to File mappings, so we extract them
        directly from the cached hierarchy. File paths are already absolute
        (resolved during Locator's cache build).
        """
        instance_hierarchy = self.locator.get_hierarchy()

        module_to_file: Dict[str, Path] = {}
        for inst_path, info in instance_hierarchy.items():
            if inst_path.startswith('_'):
                continue
            module_name = info.get('module', '')
            file_path = info.get('file', '')
            if module_name and file_path and module_name not in module_to_file:
                module_to_file[module_name] = Path(file_path)

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
        if re.fullmatch(r'p\d+', name) or name == 'empty':
            return ''
        return name

    def _annotate_rtl_with_critical_comments(self, critical_signal_mapping: Dict) -> Optional[Path]:
        """Annotate RTL source files with CRITICAL comments from critical signal mapping.

        Copies affected RTL files to <output_dir>/commented_rtl/ and inserts
        '// CRITICAL: signal1, signal2, ...' comments at the lines identified
        by synalign. Never modifies the original source files.

        Returns:
            Path to commented_rtl directory, or None if no annotations were made.
        """
        mappings = critical_signal_mapping.get('mappings', [])
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
            print('  No valid annotations')
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
                    m = re.match(r'^(\s*)', line)
                    indent = m.group(1) if m else ''
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

        return f'TODO: LLM optimization prompt for {self.design.top_module}'


if __name__ == '__main__':
    step = ExtractCriticalStep()
    step.parse_arguments()
    step.setup()
    step.step()
