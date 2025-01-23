# See LICENSE file for details

import pytest
from hagent.tool.trivial import Trivial


def test_used_dot():
    dut = Trivial()

    assert dut.error_message == ''
    assert dut.some_method_related_to_the_tool('xx') == 'xx/'

    dut.setup('potato')
    assert dut.some_method_related_to_the_tool('xx') == 'xx/'
    assert dut.error_message != ''

    dut.setup('.')
    assert dut.some_method_related_to_the_tool('xx') == 'xx.'
    assert dut.error_message == ''


if __name__ == '__main__':  # pragma: no cover
    test_used_dot()
