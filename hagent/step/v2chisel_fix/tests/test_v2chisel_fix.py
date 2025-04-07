#!/usr/bin/env python3
import os
import tempfile
import pytest
from unittest.mock import patch, MagicMock

from hagent.step.v2chisel_fix.v2chisel_fix import V2chisel_fix

@pytest.fixture
def valid_input():
    # Create a minimal valid input dictionary for V2chisel_fix.
    return {
        "chisel_pass1": {
            "chisel_changed": "class MyModule extends Module { val io = IO(new Bundle {}) }",
            "chisel_subset": "class MyModule extends Module { val io = IO(new Bundle {}) }",
            "verilog_candidate": "module mymodule(); endmodule",
            "was_valid": True
        },
        # Provide a nonempty chisel_original so that refined code is not empty.
        "chisel_original": "class MyModule extends Module { val io = IO(new Bundle {}) }",
        "verilog_fixed": "module mymodule(); endmodule",
        "llm": {"model": "test-model"}
    }

@pytest.fixture
def step_instance(valid_input):
    step = V2chisel_fix()
    # Set a dummy output file so that write_output does not fail.
    step.set_io(inp_file="dummy_input.yaml", out_file="dummy_output.yaml")
    # Inject the input_data dictionary.
    step.input_data = valid_input
    return step

def test_run_initial_equiv_pass(step_instance):
    """
    Test when the initial equivalence check passes so no refinement is needed.
    """
    # Patch _check_equivalence to always return that the candidate is equivalent.
    with patch.object(step_instance, "_check_equivalence", return_value=(True, None)):
        result = step_instance.run(step_instance.input_data)
        assert result["chisel_fixed"]["equiv_passed"] is True
        # Expect that the refined chisel equals the original chisel (or chisel_changed)
        refined = result["chisel_fixed"]["refined_chisel"]
        assert "class MyModule" in refined

def test_run_with_react_refinement(step_instance):
    """
    Test when the equivalence check fails so the React cycle is used
    and it returns a refined candidate.
    """
    # Fake equivalence check: always fail.
    def fake_check_equivalence(gold, candidate):
        return (False, "Simulated LEC failure")
    # Fake chisel-to-verilog conversion: always succeed.
    def fake_run_chisel2v(code):
        return (True, "dummy verilog", "")
    with patch.object(step_instance, "_check_equivalence", side_effect=fake_check_equivalence), \
         patch.object(step_instance, "_run_chisel2v", side_effect=fake_run_chisel2v), \
         patch("hagent.tool.react.React") as MockReact:
        mock_react = MagicMock()
        mock_react.react_cycle.return_value = "refined MyModule code"
        MockReact.return_value = mock_react
        result = step_instance.run(step_instance.input_data)
        assert result["chisel_fixed"]["equiv_passed"] is True
        assert result["chisel_fixed"]["refined_chisel"] == "refined MyModule code"

def test_run_react_failure(step_instance):
    """
    Test that if React returns an empty string (i.e. refinement fails),
    the run() method raises an error.
    """
    with patch("hagent.tool.react.React") as MockReact:
        mock_react = MagicMock()
        # Simulate React cycle failure by returning an empty string.
        mock_react.react_cycle.return_value = ""
        MockReact.return_value = mock_react
        with pytest.raises(Exception, match="React failed to refine the code."):
            step_instance.run(step_instance.input_data)
