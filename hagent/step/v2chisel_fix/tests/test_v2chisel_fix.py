import os
import subprocess
import tempfile
import pytest

from hagent.step.v2chisel_fix.v2chisel_fix import diff_code, V2chisel_fix

class DummyResult:
    def __init__(self, stdout, stderr=""):
        self.stdout = stdout
        self.stderr = stderr


def test_diff_code_invokes_diff_and_returns_output(monkeypatch, tmp_path):
    # Prepare dummy files and capture subprocess.run calls
    called = {}

    def fake_run(args, stdout, stderr, text):
        # record that diff was called with expected flags
        called['args'] = args
        return DummyResult(stdout="FAKE_DIFF")

    monkeypatch.setattr(subprocess, 'run', fake_run)
    # monkeypatch os.unlink to avoid actual deletion errors
    monkeypatch.setattr(os, 'unlink', lambda path: None)

    result = diff_code("line1\n", "line2\n")
    assert result == "FAKE_DIFF"
    # Ensure diff command was invoked correctly
    assert 'args' in called
    args = called['args']
    assert args[0] == 'diff'
    assert '-bBdNrw' in args
    assert '-U5' in args


def test_generate_diff_identical_returns_empty():
    obj = V2chisel_fix()
    # If two inputs are identical, unified diff should be empty
    diff = obj._generate_diff("a\n", "a\n")
    assert diff == ""


def test_generate_diff_simple_change_includes_diff_headers_and_lines():
    obj = V2chisel_fix()
    old = "foo\nbar\n"
    new = "foo\nbaz\n"
    diff = obj._generate_diff(old, new)
    # Should include unified-diff file labels and context
    assert '--- Original version' in diff
    assert '+++ Modified version' in diff
    # Should show removed and added lines
    assert '-bar' in diff
    assert '+baz' in diff

@pytest.mark.parametrize("old,new", [
    ("", ""),
    ("one line", "one line"),
])
def test_generate_diff_edge_cases(old, new):
    obj = V2chisel_fix()
    diff = obj._generate_diff(old, new)
    assert diff == ""
