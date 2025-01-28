# See LICENSE file for details

from hagent.tool.trivial import Trivial


def test_used_dot():
    dut = Trivial()

    assert dut._some_path == '/'
    assert dut.error_message == ''
    t = dut.some_method_related_to_the_tool('xx')
    assert t == 'xx/'
    assert dut.some_method_related_to_the_tool('xx') == 'xx/'

    x1 = dut.setup('potato')
    assert not x1
    assert dut.some_method_related_to_the_tool('xx') == 'xx/'
    assert dut.error_message != ''

    x2 = dut.setup('.')
    assert x2
    assert dut.some_method_related_to_the_tool('xx') == 'xx.'
    assert dut.error_message == ''


if __name__ == '__main__':  # pragma: no cover
    test_used_dot()
