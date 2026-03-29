#!/usr/bin/env python3
# See LICENSE for details

import importlib.util
import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Dict, Optional

from hagent.core.step import Step
from hagent.step.elab_synth_sta.common_utils import find_synth_script
from hagent.step.elab_synth_sta.config import DesignConfig, RTLConfig, StorageConfig, ToolsConfig


class Sta(Step):
    """Static Timing Analysis step: runs STA on a synthesized netlist.

    Invokes scripts/synth.py --run-sta as a subprocess.
    Expects synth.v to already exist (from the Synthesize step).

    Required YAML sections:
      - design_info.top_module
      - storage.output_dir
      - rtl.netlist_file (output from Synthesize step)

    Optional YAML fields:
      - design_info.synth_top_module
      - design_info.output_module
      - tools.liberty_file

    Output YAML fields added:
      - logs.sta_log
      - sta.frequency_mhz
    """

    def setup(self):
        super().setup()
        data = self.input_data
        assert data is not None
        self.design = DesignConfig.from_data(data, 'design_info')
        self.storage = StorageConfig.from_data(data, 'storage')
        self.rtl = RTLConfig.from_data(data, 'rtl')

        if not self.rtl.netlist_file:
            self.error('Missing required field: rtl.netlist_file (run Synthesize step first)')
        self.netlist_path = Path(self.rtl.netlist_file)

        self.tools = ToolsConfig.from_data(data, 'tools') if 'tools' in data else ToolsConfig()

    def run(self, data: Dict) -> Dict:
        output_dir = self.storage.output_dir
        if not output_dir:
            self.error('Missing required field: storage.output_dir')

        if not self.netlist_path.exists():
            self.error(f'Synthesized netlist not found: {self.netlist_path}')

        tag = self.storage.tag

        # --- Ensure synth.v is in the output dir (synth.py expects it there) ---
        output_path = Path(output_dir)
        if tag:
            output_path = output_path / tag

        expected_netlist = output_path / 'synth.v'
        if self.netlist_path.resolve() != expected_netlist.resolve():
            output_path.mkdir(parents=True, exist_ok=True)
            shutil.copy2(str(self.netlist_path), str(expected_netlist))

        # --- Find synth.py ---
        synth_script = find_synth_script()

        # --- Build command ---
        cmd = [
            sys.executable,
            str(synth_script),
            '--dir',
            output_dir,
            '--run-sta',
        ]

        if tag:
            cmd.extend(['--tag', tag])

        if self.tools.liberty_file:
            cmd.extend(['--liberty', self.tools.liberty_file])

        # Separator between synth.py args and slang args
        cmd.append('--')
        cmd.extend(['--top', self.design.effective_output_module])

        # --- Execute ---
        print(f'Running: {" ".join(cmd)}', file=sys.stderr)

        try:
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=600)
        except subprocess.TimeoutExpired:
            self.error('STA timed out after 600 seconds')

        if result.returncode != 0:
            self.error(f'STA failed (rc={result.returncode})\nstderr: {result.stderr[:500]}')

        # --- Resolve output paths ---
        sta_log = output_path / 'sta.log'

        if not sta_log.exists():
            self.error(f'Expected STA log not found: {sta_log}')

        # --- Parse frequency ---
        clock_signal = self._get_clock_signal(self.netlist_path)
        frequency_mhz = self._parse_timing_log(sta_log, clock_signal)
        print(f'STA complete, frequency: {frequency_mhz:.2f} MHz', file=sys.stderr)

        # --- Build output ---
        output = data.copy()
        logs = output.get('logs', {})
        if not isinstance(logs, dict):
            logs = {}
        logs['sta_log'] = str(sta_log)
        output['logs'] = logs

        output['sta'] = {
            'frequency_mhz': frequency_mhz,
        }

        return output

    def _get_clock_signal(self, netlist_path: Path) -> Optional[str]:
        """Get clock signal from netlist using synth.py's find_clock_signal function."""
        synth_script = find_synth_script()

        spec = importlib.util.spec_from_file_location('synth', synth_script)
        synth_module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(synth_module)

        return synth_module.find_clock_signal(str(netlist_path))

    def _parse_timing_log(self, timing_rpt_path: Path, clock_signal: Optional[str]) -> float:
        """Parse timing information from STA log and return frequency_mhz."""
        if clock_signal is None:
            print('Warning: No clock signal found, cannot parse frequency', file=sys.stderr)
            return float('inf')

        frequency = float('inf')
        try:
            content = timing_rpt_path.read_text()

            sections = re.split(r'(?=Startpoint:)', content)

            clock_section = None
            for section in sections:
                if not section.strip():
                    continue

                path_group_match = re.search(r'Path Group:\s*\**(\S+)\**', section)
                if not path_group_match:
                    continue

                path_group = path_group_match.group(1)

                if path_group == clock_signal:
                    clock_section = section
                    break

            if not clock_section:
                print('Warning: No clock path group found in timing log', file=sys.stderr)
                return frequency

            arrival_match = re.search(r'([+-]?\d+(?:\.\d+)?)\s+data arrival time\s+', clock_section, re.IGNORECASE)
            if arrival_match:
                arrival_time = float(arrival_match.group(1))
                if arrival_time > 0:
                    frequency = 1000.0 / arrival_time

        except Exception as e:
            print(f'Warning: Failed to parse timing log: {e}', file=sys.stderr)

        return frequency


if __name__ == '__main__':  # pragma: no cover
    step = Sta()
    step.parse_arguments()
    step.setup()
    step.step()
