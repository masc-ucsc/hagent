# See LICENSE for details

import pytest

from hagent.step.elab_synth_sta.elaborate import Elaborate


class TestElaborateValidation:
    def _make_step(self, tmp_path, data):
        step = Elaborate()
        step.output_file = str(tmp_path / 'output.yaml')
        step.overwrite_conf = data
        step.setup()
        return step

    def test_missing_design_info(self, tmp_path):
        with pytest.raises(ValueError, match='design_info'):
            self._make_step(tmp_path, {'rtl': {'source_dir': str(tmp_path)}, 'storage': {'output_dir': '/tmp/out'}})

    def test_missing_top_module(self, tmp_path):
        with pytest.raises(ValueError, match='design_info'):
            self._make_step(
                tmp_path,
                {
                    'design_info': {'name': 'test'},
                    'rtl': {'source_dir': str(tmp_path)},
                    'storage': {'output_dir': '/tmp/out'},
                },
            )

    def test_missing_storage_output_dir(self, tmp_path):
        with pytest.raises(ValueError, match='storage'):
            self._make_step(
                tmp_path,
                {
                    'design_info': {'top_module': 'ALU'},
                    'rtl': {'source_dir': str(tmp_path)},
                    'storage': {},
                },
            )

    def test_missing_storage_section(self, tmp_path):
        with pytest.raises(ValueError, match='storage'):
            self._make_step(
                tmp_path,
                {
                    'design_info': {'top_module': 'ALU'},
                    'rtl': {'source_dir': str(tmp_path)},
                },
            )
