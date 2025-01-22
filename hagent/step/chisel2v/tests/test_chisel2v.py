# See LICENSE for details

import os
import pytest

from hagent.step.chisel2v.chisel2v import Chisel2V


def test_chisel2v_missing_llm():
    """
    If the input YAML doesn't have 'llm', the pass should call exit(4),
    as the base Step sees an error key in the input data.
    """
    test_dir = os.path.dirname(os.path.abspath(__file__))
    inp_file = os.path.join(test_dir, 'bad_input.yaml')  # This triggers an 'error'

    step_obj = Chisel2V()
    step_obj.set_io(inp_file=inp_file, out_file='test_chisel2v_output.yaml')

    with pytest.raises(SystemExit) as exc_info:
        step_obj.setup()  # This eventually calls exit(4)
        step_obj.step()

    assert exc_info.value.code == 4


def test_chisel2v_happy_path():
    """
    With valid 'original_chisel', 'modified_verilog', and 'llm' in the YAML,
    we expect the pass to generate an updated Chisel file and store it in the output dict.
    """
    test_dir = os.path.dirname(os.path.abspath(__file__))
    inp_file = os.path.join(test_dir, 'input1.yaml')  # Contains 'original_chisel', 'modified_verilog', and 'llm'

    step_obj = Chisel2V()
    step_obj.set_io(inp_file=inp_file, out_file='test_chisel2v_output.yaml')

    step_obj.setup()
    res = step_obj.step()

    # Check the updated Chisel code
    updated_chisel = res.get('updated_chisel')
    print(f'Updated chisel code:\n{updated_chisel}')
    assert updated_chisel, "Expected non-empty 'updated_chisel' in the result"

    # Check the .scala file
    chisel_file = res.get('chisel_file')
    assert chisel_file, "Expected 'chisel_file' in the result dictionary"
    assert os.path.exists(chisel_file), f'Scala file {chisel_file} was not created'

    # Optionally, read the file to ensure it's not empty
    with open(chisel_file, 'r', encoding='utf-8') as f:
        content = f.read().strip()
        assert content, f'File {chisel_file} is empty'


if __name__ == '__main__':  # pragma: no cover
    test_chisel2v_missing_llm()
    test_chisel2v_happy_path()
