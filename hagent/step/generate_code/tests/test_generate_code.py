# See LICENSE for details

import os
import pytest

from hagent.step.generate_code.generate_code import Generate_code


def test_generate_missing_llm():
    test_dir = os.path.dirname(os.path.abspath(__file__))

    inp_file = os.path.join(test_dir, 'bad_input.yaml')

    trivial_step = Generate_code()
    trivial_step.set_io(inp_file=inp_file, out_file='test_generate_code_output.yaml')

    with pytest.raises(ValueError):
        trivial_step.setup()
        trivial_step.step()


def test_generate_code():
    test_dir = os.path.dirname(os.path.abspath(__file__))

    inp_file = os.path.join(test_dir, 'input1.yaml')

    trivial_step = Generate_code()
    trivial_step.set_io(inp_file=inp_file, out_file='test_generate_code_output.yaml')

    trivial_step.setup()

    res = trivial_step.step()

    xx = res['generated_code']
    print(f'generated_code:{xx}')

    assert len(xx) == 1


if __name__ == '__main__':  # pragma: no cover
    test_generate_missing_llm()
    test_generate_code()
