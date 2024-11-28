# See LICENSE for details

import os
from hagent.step.trivial.trivial import Trivial


def test_trivial():
    test_dir = os.path.dirname(os.path.abspath(__file__))

    inp_file = os.path.join(test_dir, 'input1.yaml')
    expected_out_file = os.path.join(test_dir, 'expected_output1.yaml')

    trivial_step = Trivial(test=True)
    trivial_step.test(inp_file=inp_file, out_file=expected_out_file)
