# hagent/step/v2chisel_fix/tests/test_v2chisel_fix.py
import pytest
from hagent.step.v2chisel_fix.v2chisel_fix import V2chisel_fix, diff_code

class DummyFix(V2chisel_fix):
    def setup(self):
        # minimal init so run() won’t crash
        self.base_metadata_context   = 5
        self.meta                    = 5
        self.input_data              = {'metadata_context': 5}
        self.input_file = self.output_file = "<dummy>"
        self.verilog_fixed_str       = ""
        self.verilog_original_str    = ""
        self.verilog_diff_str        = ""
        self.setup_called            = True

@pytest.fixture
def base_data():
    return {
        'chisel_pass1': {
            'chisel_changed': 'orig_chisel',
            'verilog_candidate': 'cand_verilog',
            'was_valid': False,
        },
        'verilog_original': '',
        'verilog_fixed': '',
        'chisel_original': 'orig_chisel',
    }

def test_skip_when_lec_flag_set(base_data):
    step = DummyFix()
    step.setup()
    data = {**base_data, 'lec': 1}
    result = step.run(data)
    assert result['lec'] == 1
    cf = result['chisel_fixed']
    assert cf['equiv_passed'] is True
    assert cf['refined_chisel'] == base_data['chisel_original']
    assert cf['chisel_diff'] == ""

def test_warn_no_fixed_and_enter_react_failure(monkeypatch, base_data):
    step = DummyFix()
    step.setup()
    data = {**base_data, 'lec': 0}
    monkeypatch.setattr(step, '_refine_chisel_code', lambda *a, **k: "")
    monkeypatch.setattr(step, '_refine_chisel_code_with_prompt4', lambda *a, **k: "")
    class FakeReact:
        def setup(self, *args, **kwargs): return True
        def react_cycle(self, *args):            return None
    monkeypatch.setattr(
        'hagent.step.v2chisel_fix.v2chisel_fix.React',
        FakeReact
    )
    result = step.run(data)
    assert result['lec'] == 0
    cf = result['chisel_fixed']
    assert cf['equiv_passed'] is False
    assert cf['refined_chisel'] == base_data['chisel_original']
    assert cf['chisel_diff'] == ""

def test_phase1_succeeds_on_first_attempt(monkeypatch, base_data):
    step = DummyFix()
    step.setup()
    data = {**base_data, 'lec': 0, 'verilog_fixed': 'fixed'}
    step._ce_calls = 0
    def fake_ce(gold, cand):
        if step._ce_calls == 0:
            step._ce_calls += 1
            return (False, 'err')
        return (True, None)
    monkeypatch.setattr(step, '_check_equivalence', fake_ce)
    monkeypatch.setattr(step, '_refine_chisel_code', lambda *a, **k: "***DIFF***")
    monkeypatch.setattr(step, '_apply_diff',       lambda o,d: "new_chisel_code")
    monkeypatch.setattr(step, '_run_chisel2v',     lambda code: (True, "verilog_out", ""))
    result = step.run(data)

    assert result['lec'] == 1
    cf = result['chisel_fixed']
    assert cf['equiv_passed'] is True
    assert cf['chisel_diff'] == "***DIFF***"
    assert cf['refined_chisel'] == "new_chisel_code"
    assert cf['metadata_context'] == step.base_metadata_context

def test_phase1_second_attempt(monkeypatch, base_data):
    step = DummyFix()
    step.setup()
    data = {**base_data, 'lec': 0, 'verilog_fixed': 'fixed'}
    step._ce_calls = 0
    def fake_ce(gold, cand):
        if step._ce_calls == 0:
            step._ce_calls += 1
            return (False, 'err')
        return (True, None)
    monkeypatch.setattr(step, '_check_equivalence', fake_ce)
    monkeypatch.setattr(step, '_refine_chisel_code',
                        lambda orig, err, att: "" if att == 1 else "++INS++")
    monkeypatch.setattr(step, '_apply_diff',   lambda o,d: "new2")
    monkeypatch.setattr(step, '_run_chisel2v', lambda c: (True, "v", ""))
    result = step.run(data)

    assert result['lec'] == 1
    assert result['chisel_fixed']['chisel_diff'] == "++INS++"

def test_phase2_succeeds(monkeypatch, base_data):
    step = DummyFix()
    step.setup()
    data = {**base_data, 'lec': 0, 'verilog_fixed': 'fixed'}
    step._ce_calls = 0
    def fake_ce(gold, cand):
        if step._ce_calls == 0:
            step._ce_calls += 1
            return (False, 'err')
        return (True, None)
    monkeypatch.setattr(step, '_check_equivalence', fake_ce)
    monkeypatch.setattr(step, '_refine_chisel_code',              lambda *a, **k: "")
    monkeypatch.setattr(step, '_refine_chisel_code_with_prompt4', lambda *a, **k: "--ADD--")
    monkeypatch.setattr(step, '_apply_diff',                      lambda o,d: "ch2")
    monkeypatch.setattr(step, '_run_chisel2v',                    lambda c: (True, "v2", ""))
    result = step.run(data)

    assert result['lec'] == 1
    cf = result['chisel_fixed']
    assert cf['chisel_diff'] == "--ADD--"
    assert cf['refined_chisel'] == "ch2"

def test_diff_code_roundtrip(tmp_path):
    t1 = "line1\nfoo\n"
    t2 = "line1\nbar\n"
    out = diff_code(t1, t2)
    assert "-foo" in out and "+bar" in out
