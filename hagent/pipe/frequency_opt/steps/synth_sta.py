# See LICENSE for details
"""
Synthesis step: RTL synthesis via scripts/synth.py.

This step is reusable for both initial synthesis and re-synthesis
of optimized RTL. The behavior is controlled by YAML fields.
"""

import importlib.util
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Dict, Optional

from hagent.core.step import Step
from hagent.pipe.frequency_opt.schema import (
    BenchmarkConfig,
    RTLSourceConfig,
    ToolsConfig,
    StorageConfig,
    get_field,
    set_field,
)


class SynthSTAStep(Step):
    """
    Synthesis plus STA step: runs RTL synthesis then static timing analysis using scripts/synth.py.

    Required YAML sections:
      - benchmark: top_module
      - rtl: source_dir (used if optimized.rtl_dir not set)
      - storage: output_dir

    Optional YAML fields:
      - optimized.rtl_dir: Use this instead of rtl.source_dir for re-synthesis
      - rtl: manifest_file
      - synth_sta_tag: Tag for this run (default: 'baseline')

    Writes to YAML:
      - synthesis.netlist_path
      - synthesis.elab_path
      - synthesis.log_path
      - synthesis.tag
      - sta.report_path
      - sta.frequency_mhz
    """

    def run(self, data: Dict) -> Dict:
        # Parse configuration
        benchmark = BenchmarkConfig.from_data(data, 'benchmark')
        rtl = RTLSourceConfig.from_data(data, 'rtl')
        tools = ToolsConfig.from_data(data, 'tools')
        storage = StorageConfig.from_data(data, 'storage')

        # Check for optimized RTL (for re-synthesis)
        optimized_rtl_dir = get_field(data, 'optimized.rtl_dir')
        rtl_dir = optimized_rtl_dir if optimized_rtl_dir else rtl.source_dir

        # Validate RTL directory exists
        rtl_path = Path(rtl_dir)
        if not rtl_path.exists():
            self.error(f'RTL directory does not exist: {rtl_dir}')

        # Synthesis tag for output organization
        tag = get_field(data, 'synthesis_tag', 'baseline')

        # Build output paths
        output_dir = Path(storage.output_dir) / 'synth-sta'
        if output_dir.exists():
            shutil.rmtree(output_dir)

        output_dir.mkdir(parents=True, exist_ok=False)

        # Locate synth.py script
        synth_script = self._find_synth_script()

        # STA command (note that synth.py's run-sta includes elab, synthesis, and sta)
        synth_top = benchmark.effective_synth_top
        cmd = [
            sys.executable,
            str(synth_script),
            '--dir',
            str(output_dir),
            '--elab-method',
            tools.elab_method,
            '--top-synthesis',
            synth_top,
            '--run-sta',
            '--liberty',
            tools.liberty_file,
            '--tag',
            tag,
        ]

        if benchmark.output_module is not None:
            cmd.extend(['--output-module', benchmark.output_module])

        cmd.extend(
            [
                '--',
                '--top',
                benchmark.top_module,
            ]
        )

        if rtl.standalone_files is not None:
            cmd.extend(rtl.standalone_files)

        # If the filelist file is provided in the config, we use it to gather
        # all RTL source files that we need; otherwise, we assume it's all files
        # that matches file patterns under `rtl_path`.
        if rtl.manifest_file is not None:
            cmd.extend(['-f', rtl.manifest_file])
        else:
            rtl_files = []
            for pattern in rtl.file_patterns:
                rtl_files.extend([str(f) for f in rtl_path.glob(pattern)])

            if not rtl_files:
                self.error(f'No RTL files found in {rtl_dir} matching {rtl.file_patterns}')

            cmd.extend(rtl_files)

        print('Running synthesis and STA:')
        print(f'  Top module: {benchmark.top_module}')
        print(f'  RTL source: {rtl_dir}')
        print(f'  Output: {output_dir}')
        print(f'  Command: {" ".join(cmd[:8])}...')

        # Run synthesis
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=3600)

        if result.returncode != 0:
            print(f'Synthesis + STA stderr:\n{result.stderr}')
            self.error(f'Synthesis + STA failed with return code {result.returncode}')

        # Verify outputs exist
        netlist_path = output_dir / tag / 'synth.v'
        elab_path = output_dir / tag / 'elab.v'
        synth_log_path = output_dir / tag / 'synth.log'
        sta_report_path = output_dir / tag / 'sta.log'

        hierarchy_path = output_dir / tag / 'hierarchy.txt'

        if not netlist_path.exists():
            self.error(f'Synthesis did not produce netlist: {netlist_path}')
        if not sta_report_path.exists():
            self.error(f'STA did not produce timing report: {sta_report_path}')
        if not hierarchy_path.exists():
            # we don't error out because hierarchy.txt won't be produced by synth.py
            # if the elab top module is the same as the synth top module
            print(f'Warning: Elaboration did not produce hierarchy file: {hierarchy_path}')

        clock_signal = self._get_clock_signal(netlist_path)
        frequency = self._parse_timing_log(sta_report_path, clock_signal)
        print('Synthesis + STA completed:')
        print(f'  Netlist: {netlist_path}')
        print(f'  Elab: {elab_path}')
        print(f'  Timing report: {sta_report_path}')
        print(f'  Frequency: {frequency:.2f} MHz')

        # Build output YAML
        output = data.copy()
        set_field(output, 'synthesis.netlist_path', str(netlist_path))
        set_field(output, 'synthesis.elab_path', str(elab_path))
        set_field(output, 'synthesis.log_path', str(synth_log_path))
        set_field(output, 'synthesis.tag', tag)
        set_field(output, 'synthesis.hierarchy_path', str(hierarchy_path))
        set_field(output, 'sta.report_path', str(sta_report_path))
        set_field(output, 'sta.frequency_mhz', frequency)

        return output

    def _find_synth_script(self) -> Path:
        """Find the synth.py script in the hagent repository."""
        # Try relative to this file
        this_file = Path(__file__).resolve()
        # Go up from hagent/pipe/frequency_opt/steps/ to hagent root, then to scripts/
        hagent_root = this_file.parent.parent.parent.parent.parent
        synth_script = hagent_root / 'scripts' / 'synth.py'

        if synth_script.exists():
            return synth_script

        # Fallback: try HAGENT_ROOT_DIR
        repo_dir = os.environ.get('HAGENT_ROOT_DIR')
        if repo_dir:
            synth_script = Path(repo_dir) / 'scripts' / 'synth.py'
            if synth_script.exists():
                return synth_script

        self.error('Cannot find scripts/synth.py. Set HAGENT_ROOT_DIR or run from hagent directory.')

    def _get_clock_signal(self, netlist_path: Path) -> Optional[str]:
        """Get clock signal from netlist using synth.py's find_clock_signal function."""
        synth_script = self._find_synth_script()

        # Import find_clock_signal from synth.py
        spec = importlib.util.spec_from_file_location('synth', synth_script)
        synth_module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(synth_module)

        return synth_module.find_clock_signal(str(netlist_path))

    def _parse_timing_log(self, timing_rpt_path: Path, clock_signal: Optional[str]) -> float:
        """
        Parse timing information from STA log and returns frequency_mhz.

        Focuses on the timing report section where Path Group matches the `clock_signal`.
        """
        if clock_signal is None:
            self.error('Currently only support report with clock signals')

        frequency = float('inf')
        try:
            content = timing_rpt_path.read_text()

            # Split content into timing report sections by "Startpoint:"
            sections = re.split(r'(?=Startpoint:)', content)

            # Find the section with the clock path group (not async_default)
            clock_section = None
            for section in sections:
                if not section.strip():
                    continue

                # Extract Path Group from this section
                path_group_match = re.search(r'Path Group:\s*\**(\S+)\**', section)
                if not path_group_match:
                    continue

                path_group = path_group_match.group(1)

                if path_group == clock_signal:
                    clock_section = section
                    break

            if not clock_section:
                print('Warning: No clock path group found in timing log')
                return frequency

            # Parse timing from the clock section
            # Extract arrival time -> calculate frequency
            arrival_match = re.search(r'([+-]?\d+(?:\.\d+)?)\s+data arrival time\s+', clock_section, re.IGNORECASE)
            if arrival_match:
                arrival_time = float(arrival_match.group(1))
                if arrival_time > 0:
                    frequency = 1000.0 / arrival_time  # Convert to MHz (assuming ns)

        except Exception as e:
            print(f'Warning: Failed to parse timing log: {e}')

        return frequency


if __name__ == '__main__':
    step = SynthSTAStep()
    step.parse_arguments()
    step.setup()
    step.step()
