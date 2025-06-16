# hagent/step/v2chisel_fix/tests/test_v2chisel_fix_cli.py
import sys
import yaml
import types
import sys
import pytest

# Stub out the heavy LLM wrapper to avoid pulling optional dependencies during
# tests.  The CLI test only verifies basic wiring and does not exercise LLM
# functionality.
class DummyWrap:
    def __init__(self, *args, **kwargs):
        self.total_cost = 0.0
        self.total_tokens = 0
        self.responses = []
    def inference(self, *args, **kwargs):
        return []


# Provide a stub for the deprecated `Unified_diff` module so that importing
# `v2chisel_fix` succeeds during test collection.
stub = types.ModuleType('unified_diff')
stub.Unified_diff = object
sys.modules.setdefault('hagent.step.unified_diff.unified_diff', stub)

import hagent.step.v2chisel_fix.v2chisel_fix as v2_mod
from hagent.step.v2chisel_fix.v2chisel_fix import V2chisel_fix

def write_yaml(data, path):
    with open(path, "w") as f:
        yaml.safe_dump(data, f)

@pytest.fixture
def pass1_yaml(tmp_path):
    data = {
        "chisel_pass1": {
            "chisel_changed":   "class Top extends Module { }",
            "verilog_candidate": "module Top(); endmodule",
            "was_valid":        False,
        },
        "verilog_original": "module Top(); endmodule",
        "verilog_fixed":    "module Top(); endmodule",
        "chisel_original":  "class Top extends Module { }",
    }
    p = tmp_path / "in.yaml"
    write_yaml(data, p)
    return p

def test_cli_generates_equivalent_chisel(tmp_path, pass1_yaml, monkeypatch):
    out_yaml = tmp_path / "out.yaml"

    # Use the dummy LLM wrapper to avoid optional dependencies like diskcache.
    monkeypatch.setattr(v2_mod, "LLM_wrap", DummyWrap)

    # stub out _check_equivalence to always pass immediately
    monkeypatch.setattr(
        V2chisel_fix,
        "_check_equivalence",
        lambda self, gold, cand: (True, None)
    )

    # Simulate CLI invocation: set sys.argv and then call parse_arguments()
    monkeypatch.setattr(sys, "argv", ["v2chisel_fix", str(pass1_yaml), "-o", str(out_yaml)])

    step = V2chisel_fix()
    step.parse_arguments()  # now reads from sys.argv
    step.setup()
    result_dict = step.step()

    # Ensure the file was written
    assert out_yaml.exists()

    # Load and compare
    on_disk = yaml.safe_load(out_yaml.read_text())
    assert result_dict == on_disk

    # Because we stubbed equivalence to pass:
    assert on_disk["lec"] == 1
    cf = on_disk["chisel_fixed"]
    assert cf["equiv_passed"] is True
    # No refinement needed
    assert cf["refined_chisel"] == "class Top extends Module { }"
    assert cf["chisel_diff"] == ""
