#!/usr/bin/env python3
# See LICENSE for details

import sys
from typing import Dict

from hagent.core.step import Step


class SynthSTA(Step):
    """Synth/STA step: chains Elaborate, Synthesize, and Sta steps.

    Convenience wrapper that runs all three phases in sequence and produces
    backward-compatible output under the 'synth_sta' key. Although it violates
    the 'hermetic' principle, elab->synth->sta chaining just occur too frequently.

    Required YAML sections:
      - design_info.top_module
      - storage.output_dir
      - rtl.manifest_file OR rtl.standalone_files OR rtl.source_dir (at least one)

    Optional YAML fields:
      - design_info.name
      - design_info.synth_top_module
      - design_info.output_module
      - rtl.source_dir (glob *.sv/*.v from this directory)
      - rtl.elab_method (auto/slang/sv2v/none, default: auto)
      - storage.tag
      - tools.liberty_file

    Output YAML fields added:
      - synth_sta.elab_path
      - synth_sta.netlist_path
      - synth_sta.sta_log
      - synth_sta.synth_log
      - synth_sta.frequency_mhz
      - rtl.elab_file, rtl.netlist_file (from Elaborate/Synthesize)
      - logs.* (elab_log, synth_log, sta_log)
      - sta.frequency_mhz
    """

    def setup(self):
        super().setup()

    def run(self, data: Dict) -> Dict:
        from hagent.step.elab_synth_sta.elaborate import Elaborate
        from hagent.step.elab_synth_sta.sta import Sta
        from hagent.step.elab_synth_sta.synthesize import Synthesize
        from hagent.workflow.workflow import Workflow

        wf = Workflow()
        wf.output_file = self.output_file
        elab = wf.add_step('elaborate', Elaborate())
        synth = wf.add_step('synthesize', Synthesize())
        sta = wf.add_step('sta', Sta())
        wf.chain(elab, synth, sta)

        result = wf.run(data)

        # Propagate sub-step errors as ValueError (backward compatibility)
        if result.get('__workflow_status__') == 'error':
            raise ValueError(result.get('__workflow_error__', 'workflow error'))

        # Build backward-compatible synth_sta output key
        rtl = result.get('rtl', {})
        logs = result.get('logs', {})
        sta_out = result.get('sta', {})

        result['synth_sta'] = {
            'elab_path': rtl.get('elab_file', ''),
            'netlist_path': rtl.get('netlist_file', ''),
            'sta_log': logs.get('sta_log', ''),
            'synth_log': logs.get('synth_log', ''),
            'frequency_mhz': sta_out.get('frequency_mhz', float('inf')),
        }

        print(f'Frequency: {sta_out.get("frequency_mhz", float("inf")):.2f} MHz', file=sys.stderr)

        return result


if __name__ == '__main__':  # pragma: no cover
    step = SynthSTA()
    step.parse_arguments()
    step.setup()
    step.step()
