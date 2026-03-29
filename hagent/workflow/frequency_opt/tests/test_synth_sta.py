# See LICENSE for details

import pytest

from hagent.workflow.frequency_opt.steps.synth_sta import SynthSTA


class TestSynthStaValidation:
    def _make_step(self, tmp_path, data):
        step = SynthSTA()
        step.output_file = str(tmp_path / 'output.yaml')
        step.overwrite_conf = data
        step.setup()
        return step

    def test_missing_design_info(self, tmp_path):
        step = self._make_step(tmp_path, {'rtl': {'source_dir': '/tmp'}, 'storage': {'output_dir': '/tmp/out'}})
        with pytest.raises(ValueError, match='design_info'):
            step.run(step.input_data)

    def test_missing_top_module(self, tmp_path):
        step = self._make_step(
            tmp_path,
            {
                'design_info': {'name': 'test'},
                'rtl': {'source_dir': '/tmp'},
                'storage': {'output_dir': '/tmp/out'},
            },
        )
        with pytest.raises(ValueError, match='design_info'):
            step.run(step.input_data)

    def test_missing_storage_output_dir(self, tmp_path):
        step = self._make_step(
            tmp_path,
            {
                'design_info': {'top_module': 'ALU'},
                'rtl': {'source_dir': '/tmp'},
                'storage': {},
            },
        )
        with pytest.raises(ValueError, match='storage'):
            step.run(step.input_data)

    def test_missing_storage_section(self, tmp_path):
        step = self._make_step(
            tmp_path,
            {
                'design_info': {'top_module': 'ALU'},
                'rtl': {'standalone_files': ['alu.v'], 'source_dir': str(tmp_path)},
            },
        )
        with pytest.raises(ValueError, match='storage'):
            step.run(step.input_data)
