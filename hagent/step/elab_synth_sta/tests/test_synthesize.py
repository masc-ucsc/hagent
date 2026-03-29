# See LICENSE for details

import pytest

from hagent.step.elab_synth_sta.synthesize import Synthesize


class TestSynthesizeValidation:
    def _make_step(self, tmp_path, data):
        step = Synthesize()
        step.output_file = str(tmp_path / 'output.yaml')
        step.overwrite_conf = data
        step.setup()
        return step

    def test_missing_design_info(self, tmp_path):
        with pytest.raises(ValueError, match='design_info'):
            self._make_step(tmp_path, {'rtl': {'source_dir': '/tmp'}, 'storage': {'output_dir': '/tmp/out'}})

    def test_missing_storage_output_dir(self, tmp_path):
        with pytest.raises(ValueError, match='storage'):
            self._make_step(
                tmp_path,
                {
                    'design_info': {'top_module': 'ALU'},
                    'rtl': {'source_dir': '/tmp'},
                    'storage': {},
                },
            )

    def test_missing_elab_file(self, tmp_path):
        with pytest.raises(ValueError, match='rtl.elab_file'):
            self._make_step(
                tmp_path,
                {
                    'design_info': {'top_module': 'ALU'},
                    'storage': {'output_dir': str(tmp_path / 'out')},
                    'rtl': {'source_dir': str(tmp_path)},
                },
            )

    def test_elab_file_not_found(self, tmp_path):
        step = self._make_step(
            tmp_path,
            {
                'design_info': {'top_module': 'ALU'},
                'storage': {'output_dir': str(tmp_path / 'out')},
                'rtl': {'elab_file': '/nonexistent/elab.v', 'source_dir': str(tmp_path)},
            },
        )
        with pytest.raises(ValueError, match='Elaboration file not found'):
            step.run(step.input_data)
