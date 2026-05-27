#!/usr/bin/env python3
# See LICENSE for details

import shutil
import subprocess
import sys
from pathlib import Path
from typing import Dict

from hagent.core.step import Step
from hagent.step.elab_synth_sta.common_utils import find_synth_script
from hagent.step.elab_synth_sta.config import DesignConfig, RTLConfig, StorageConfig, ToolsConfig


class Synthesize(Step):
    """Synthesis step: maps elaborated netlist to a technology library.

    Invokes scripts/synth.py --run-synth as a subprocess.
    Expects elab.v to already exist (from the Elaborate step).

    Required YAML sections:
      - design_info.top_module
      - storage.output_dir
      - rtl.elab_file (output from Elaborate step)

    Optional YAML fields:
      - design_info.synth_top_module
      - design_info.output_module
      - tools.liberty_file

    Output YAML fields added:
      - rtl.netlist_file
      - logs.synth_log
    """

    def setup(self):
        super().setup()
        data = self.input_data
        assert data is not None
        self.design = DesignConfig.from_data(data, 'design_info')
        self.storage = StorageConfig.from_data(data, 'storage')
        self.rtl = RTLConfig.from_data(data, 'rtl')

        if not self.rtl.elab_file:
            self.error('Missing required field: rtl.elab_file (run Elaborate step first)')
        self.elab_path = Path(self.rtl.elab_file)

        self.tools = ToolsConfig.from_data(data, 'tools') if 'tools' in data else ToolsConfig()

    def run(self, data: Dict) -> Dict:
        output_dir = self.storage.output_dir
        if not output_dir:
            self.error('Missing required field: storage.output_dir')

        if not self.elab_path.exists():
            self.error(f'Elaboration file not found: {self.elab_path}')

        tag = self.storage.tag

        # --- Ensure elab.v is in the output dir (synth.py expects it there) ---
        output_path = Path(output_dir)
        if tag:
            output_path = output_path / tag

        expected_elab = output_path / 'elab.v'
        if self.elab_path.resolve() != expected_elab.resolve():
            output_path.mkdir(parents=True, exist_ok=True)
            shutil.copy2(str(self.elab_path), str(expected_elab))

        # --- Find synth.py ---
        synth_script = find_synth_script()

        # --- Build command ---
        cmd = [
            sys.executable,
            str(synth_script),
            '--dir',
            output_dir,
            '--run-synth',
            '--skip-elab',
        ]

        if tag:
            cmd.extend(['--tag', tag])

        if self.tools.liberty_file:
            cmd.extend(['--liberty', self.tools.liberty_file])

        if self.design.synth_top_module and self.design.synth_top_module != self.design.top_module:
            cmd.extend(['--top-synthesis', self.design.synth_top_module])

        if self.design.output_module and self.design.output_module != self.design.effective_synth_top:
            cmd.extend(['--output-module', self.design.output_module])

        # Separator between synth.py args and slang args
        cmd.append('--')
        cmd.extend(['--top', self.design.top_module])

        # --- Execute ---
        print(f'Running: {" ".join(cmd)}', file=sys.stderr)

        try:
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=3600)
        except subprocess.TimeoutExpired:
            self.error('Synthesis timed out after 3600 seconds')

        if result.returncode != 0:
            self.error(f'Synthesis failed (rc={result.returncode})\nstderr: {result.stderr[:500]}')

        # --- Resolve output paths ---
        netlist_path = output_path / 'synth.v'
        synth_log = output_path / 'synth.log'

        if not netlist_path.exists():
            self.error(f'Expected synthesis output not found: {netlist_path}')

        print(f'Synthesis complete: {netlist_path}', file=sys.stderr)

        # --- Build output ---
        output = data.copy()
        rtl = output.get('rtl', {})
        if not isinstance(rtl, dict):
            rtl = {}
        rtl['netlist_file'] = str(netlist_path)
        output['rtl'] = rtl

        logs = output.get('logs', {})
        if not isinstance(logs, dict):
            logs = {}
        logs['synth_log'] = str(synth_log)
        output['logs'] = logs

        return output


if __name__ == '__main__':  # pragma: no cover
    step = Synthesize()
    step.parse_arguments()
    step.setup()
    step.step()
