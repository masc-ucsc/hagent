"""Tests for hagent.runner.render."""

from hagent.runner.render import format_duration, print_result


class TestFormatDuration:
    def test_seconds(self):
        assert format_duration(2.1) == '2.1s'

    def test_subsecond(self):
        assert format_duration(0.3) == '0.3s'

    def test_minutes(self):
        assert format_duration(72.5) == '1m12s'

    def test_exact_minute(self):
        assert format_duration(60.0) == '1m0s'


class TestPrintResult:
    def test_pass(self, capsys):
        print_result('compile', 0, 2.1)
        captured = capsys.readouterr()
        assert 'PASS' in captured.err
        assert 'compile' in captured.err
        assert '2.1s' in captured.err

    def test_fail_with_log(self, capsys):
        print_result('compile', 1, 12.4, log_path='/tmp/logs/compile.log', tag_name='tst1')
        captured = capsys.readouterr()
        assert 'FAIL' in captured.err
        assert '/tmp/logs/compile.log' in captured.err
        assert 'repro:' in captured.err

    def test_fail_verbose(self, capsys):
        print_result('compile', 1, 1.0, stderr_tail='line1\nline2', tag_name='tst1', verbose=True)
        captured = capsys.readouterr()
        assert '| line1' in captured.err
        assert '| line2' in captured.err
