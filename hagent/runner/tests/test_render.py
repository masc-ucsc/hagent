"""Tests for hagent.runner.render."""

import json
import os

from hagent.runner.render import append_jsonl, build_result_record, format_duration, print_result


class TestFormatDuration:
    def test_seconds(self):
        assert format_duration(2.1) == '2.1s'

    def test_subsecond(self):
        assert format_duration(0.3) == '0.3s'

    def test_minutes(self):
        assert format_duration(72.5) == '1m12s'

    def test_exact_minute(self):
        assert format_duration(60.0) == '1m0s'


class TestBuildResultRecord:
    def test_pass_record(self):
        r = build_result_record('compile', 0, 2.1, '/tmp/log', 'tst1')
        assert r['step'] == 'compile'
        assert r['status'] == 'PASS'
        assert r['exit_code'] == 0
        assert r['duration'] == 2.1

    def test_fail_record(self):
        r = build_result_record('synth', 1, 5.0)
        assert r['status'] == 'FAIL'


class TestAppendJsonl:
    def test_append(self, tmp_path):
        tag_dir = str(tmp_path / 'tag1')
        os.makedirs(tag_dir)
        record = build_result_record('compile', 0, 2.1)
        append_jsonl(tag_dir, record)
        append_jsonl(tag_dir, record)
        jsonl_path = os.path.join(tag_dir, 'runner_results.jsonl')
        with open(jsonl_path) as f:
            lines = f.readlines()
        assert len(lines) == 2
        assert json.loads(lines[0])['step'] == 'compile'


class TestPrintResult:
    def test_pass(self, capsys):
        print_result('compile', 0, 2.1)
        captured = capsys.readouterr()
        assert 'PASS' in captured.err
        assert 'compile' in captured.err
        assert '2.1s' in captured.err
        # JSONL on stdout
        data = json.loads(captured.out)
        assert data['status'] == 'PASS'

    def test_fail_with_log(self, capsys):
        print_result('compile', 1, 12.4, log_path='/tmp/logs/compile.log', tag_name='tst1')
        captured = capsys.readouterr()
        assert 'FAIL' in captured.err
        assert '/tmp/logs/compile.log' in captured.err
        assert 'repro:' in captured.err
        assert '@tst1' in captured.err

    def test_fail_verbose(self, capsys):
        print_result('compile', 1, 1.0, stderr_tail='line1\nline2', tag_name='tst1', verbose=True)
        captured = capsys.readouterr()
        assert '| line1' in captured.err
        assert '| line2' in captured.err

    def test_jsonl_written_to_tag(self, tmp_path, capsys):
        tag_dir = str(tmp_path / 'tag1')
        os.makedirs(tag_dir)
        print_result('hello', 0, 1.0, tag_dir=tag_dir)
        jsonl_path = os.path.join(tag_dir, 'runner_results.jsonl')
        assert os.path.exists(jsonl_path)
