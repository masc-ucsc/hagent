#!/usr/bin/env python3
# See LICENSE for details

import subprocess
import sys
from pathlib import Path
from typing import Dict

from hagent.core.step import Step
from hagent.step.elab_synth_sta.common_utils import find_synth_script
from hagent.step.elab_synth_sta.config import DesignConfig, RTLConfig, StorageConfig


class Elaborate(Step):
    """Elaboration step: converts RTL sources into a flattened Verilog netlist.

    Invokes scripts/synth.py --run-elab as a subprocess.

    Required YAML sections:
      - design.top_module
      - storage.output_dir
      - rtl.manifest_file OR rtl.standalone_files OR rtl.source_dir

    Optional YAML fields:
      - design_info.synth_top_module
      - design_info.output_module
      - rtl.elab_method (auto/slang/sv2v/none)
      - storage.tag

    Output YAML fields added:
      - rtl.elab_file
      - logs.elab_log
    """

    def setup(self):
        super().setup()
        data = self.input_data
        assert data is not None
        self.design = DesignConfig.from_data(data, 'design_info')
        self.rtl = RTLConfig.from_data(data, 'rtl')
        self.storage = StorageConfig.from_data(data, 'storage')

    def run(self, data: Dict) -> Dict:
        # --- Validate storage ---
        output_dir = self.storage.output_dir
        if not output_dir:
            self.error('Missing required field: storage.output_dir')

        # --- Validate RTL ---
        manifest_file = self.rtl.manifest_file
        standalone_files = self.rtl.standalone_files
        source_dir = self.rtl.source_dir

        if not manifest_file and not standalone_files and not source_dir:
            self.error('Must provide rtl.manifest_file, rtl.standalone_files, or rtl.source_dir')

        elab_method = self.rtl.elab_method
        tag = self.storage.tag

        # --- Find synth.py ---
        synth_script = find_synth_script()

        # --- Build command ---
        cmd = [
            sys.executable,
            str(synth_script),
            '--dir',
            output_dir,
            '--run-elab',
        ]

        if tag:
            cmd.extend(['--tag', tag])

        cmd.extend(['--top-synthesis', self.design.effective_synth_top])

        cmd.extend(['--output-module', self.design.effective_output_module])

        if elab_method:
            cmd.extend(['--elab-method', elab_method])

        # Separator between synth.py args and slang args
        cmd.append('--')
        cmd.extend(['--top', self.design.top_module])

        source_dir_files = []
        should_use_source_files = elab_method == 'sv2v' or elab_method == 'none'
        if source_dir and should_use_source_files:
            source_path = Path(source_dir)
            file_patterns = ['*.sv', '*.v']
            for pattern in file_patterns:
                source_dir_files.extend([str(f) for f in source_path.glob(pattern)])
            if standalone_files:
                source_dir_files.extend([f for f in standalone_files])

        if not should_use_source_files and manifest_file:
            cmd.extend(['-F', manifest_file])

        if standalone_files:
            cmd.extend(standalone_files)

        if source_dir_files:
            cmd.extend(source_dir_files)

        # --- Execute ---
        print(f'Running: {" ".join(cmd)}', file=sys.stderr)

        try:
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=1800)
        except subprocess.TimeoutExpired:
            self.error('Elaboration timed out after 1800 seconds')

        if result.returncode != 0:
            self.error(f'Elaboration failed (rc={result.returncode})\nstderr: {result.stderr[:500]}')

        # --- Resolve output paths ---
        output_path = Path(output_dir)
        if tag:
            output_path = output_path / tag

        elab_path = output_path / 'elab.v'
        elab_log = output_path / 'elab.log'

        if not elab_path.exists():
            self.error(f'Expected elaboration output not found: {elab_path}')

        print(f'Elaboration complete: {elab_path}', file=sys.stderr)

        # --- Build output ---
        output = data.copy()
        rtl_out = output.get('rtl', {})
        if not isinstance(rtl_out, dict):
            rtl_out = {}
        rtl_out['elab_file'] = str(elab_path)
        output['rtl'] = rtl_out

        logs = output.get('logs', {})
        if not isinstance(logs, dict):
            logs = {}
        logs['elab_log'] = str(elab_log)
        output['logs'] = logs

        return output


if __name__ == '__main__':  # pragma: no cover
    step = Elaborate()
    step.parse_arguments()
    step.setup()
    step.step()
