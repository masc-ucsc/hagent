# See LICENSE for details

import os
import pytest

from hagent.step.replicate_code.replicate_code import Replicate_code


def test_replicate_missing_llm():
    test_dir = os.path.dirname(os.path.abspath(__file__))

    inp_file = os.path.join(test_dir, 'bad_input.yaml')

    trivial_step = Replicate_code()
    trivial_step.set_io(inp_file=inp_file, out_file='test_replicate_code_output.yaml')

    with pytest.raises(ValueError):
        trivial_step.setup()
        trivial_step.step()


def test_replicate_code():
    test_dir = os.path.dirname(os.path.abspath(__file__))

    inp_file = os.path.join(test_dir, 'input1.yaml')

    trivial_step = Replicate_code()
    trivial_step.set_io(inp_file=inp_file, out_file='test_replicate_code_output.yaml')

    trivial_step.setup()

    res = trivial_step.step()

    xx = res['optimized']
    print(f'optimized:{xx}')

    assert len(xx) == 2


if __name__ == '__main__':  # pragma: no cover
    test_replicate_missing_llm()
    test_replicate_code()
