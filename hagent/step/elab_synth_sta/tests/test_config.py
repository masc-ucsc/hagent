# See LICENSE for details

import pytest

from hagent.step.elab_synth_sta.config import DesignConfig


class TestDesignConfig:
    def test_defaults(self):
        cfg = DesignConfig(top_module='ALU')
        assert cfg.name == ''
        assert cfg.top_module == 'ALU'
        assert cfg.synth_top_module is None
        assert cfg.output_module is None

    def test_effective_synth_top_defaults_to_top_module(self):
        cfg = DesignConfig(top_module='ALU')
        assert cfg.effective_synth_top == 'ALU'

    def test_effective_synth_top_uses_synth_top_module(self):
        cfg = DesignConfig(top_module='CPU', synth_top_module='ALU')
        assert cfg.effective_synth_top == 'ALU'

    def test_effective_output_module_defaults_to_synth_top(self):
        cfg = DesignConfig(top_module='CPU', synth_top_module='ALU')
        assert cfg.effective_output_module == 'ALU'

    def test_effective_output_module_uses_output_module(self):
        cfg = DesignConfig(top_module='CPU', output_module='ALU_out')
        assert cfg.effective_output_module == 'ALU_out'

    def test_missing_top_module_raises(self):
        with pytest.raises(Exception):
            DesignConfig()
