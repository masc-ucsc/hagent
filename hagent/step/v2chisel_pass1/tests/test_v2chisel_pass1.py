# See LICENSE for details

import os
import pytest

from hagent.step.v2chisel_pass1.v2chisel_pass1 import V2ChiselPass1


def test_v2chisel_missing_llm():
    """
    If the input YAML doesn't have 'llm', the pass should raise ValueError.
    """
    test_dir = os.path.dirname(os.path.abspath(__file__))
    inp_file = os.path.join(test_dir, 'bad_input.yaml')

    step_obj = V2ChiselPass1()
    step_obj.set_io(inp_file=inp_file, out_file='test_v2chiselpass1_output.yaml')

    with pytest.raises(ValueError, match="Missing 'llm' section"):
        step_obj.setup()
        step_obj.step()


def test_v2chisel_code():
    """
    With a valid YAML (including 'llm'), we run the pass and verify
    the final output dictionary has 'chisel_pass1' with the expected fields.
    """
    test_dir = os.path.dirname(os.path.abspath(__file__))
    inp_file = os.path.join(test_dir, 'input1.yaml')

    step_obj = V2ChiselPass1()
    step_obj.set_io(inp_file=inp_file, out_file='test_v2chiselpass1_output.yaml')

    step_obj.setup()
    res = step_obj.step()

    # The pass stores final data in 'chisel_pass1' by design
    chisel_data = res.get('chisel_pass1', {})
    print(f'[TEST] chisel_pass1:\n{chisel_data}')

    # Check that we got something
    assert chisel_data, "Expected 'chisel_pass1' key in output"

    # The pass should store 'chisel_changed', 'verilog_candidate', 'was_valid'
    assert 'chisel_changed' in chisel_data, "Expected 'chisel_changed' in chisel_pass1"
    assert 'verilog_candidate' in chisel_data, "Expected 'verilog_candidate' in chisel_pass1"
    assert 'was_valid' in chisel_data, "Expected 'was_valid' in chisel_pass1"

    # Optional: check that was_valid is True or that there's some minimal snippet
    # If there's no real LLM or chisel2v environment, this might fail or produce empty strings
    # because it can't generate real code. But let's do a minimal check:
    assert chisel_data['chisel_changed'], 'chisel_changed is empty'
    assert chisel_data['verilog_candidate'], 'verilog_candidate is empty'


if __name__ == '__main__':  # pragma: no cover
    test_v2chisel_missing_llm()
    test_v2chisel_code()
