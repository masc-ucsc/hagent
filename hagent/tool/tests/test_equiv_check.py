import os
import pytest
import shutil
from hagent.tool.equiv_check import Equiv_check


@pytest.fixture
def prepare_checker():
    """
    Fixture to instantiate the checker and ensure a clean workspace before each test.
    """
    # Cleanup before test runs:
    if os.path.isdir("equiv_check"):
        shutil.rmtree("equiv_check")
    checker = Equiv_check()
    return checker

def test_setup_failure(prepare_checker):
    """
    Tests setup with an invalid Yosys path, expecting failure and proper error message.
    """
    checker = prepare_checker
    result = checker.setup(yosys_path="nonexistent_yosys_binary")
    assert result is False
    assert checker.yosys_installed is False
    assert "Yosys not found" in checker.get_error()

def test_setup_success(prepare_checker, monkeypatch):
    """
    Tests setup with a mocked 'yosys -V' call that simulates success.
    """
    def mock_run(*args, **kwargs):
        class MockCompleted:
            returncode = 0
            stdout = "Yosys 0.9+ (mocked)"
            stderr = ""
        return MockCompleted()

    monkeypatch.setattr("subprocess.run", mock_run)

    checker = prepare_checker
    result = checker.setup()  # no specific path; mock ensures success
    assert result is True
    assert checker.yosys_installed is True
    assert checker.get_error() == ""

def test_no_module(prepare_checker):
    """
    If no module is found, a ValueError is raised.
    """
    checker = prepare_checker
    checker.yosys_installed = True
    no_module_code = "// Just a comment, no modules."

    with pytest.raises(ValueError):
        checker.check_equivalence(no_module_code, "module top(); endmodule")

def test_multiple_modules(prepare_checker):
    """
    If more than one module is found, a ValueError is raised.
    """
    checker = prepare_checker
    checker.yosys_installed = True
    multi_module = """
module m1();
endmodule

module m2();
endmodule
"""
    with pytest.raises(ValueError):
        checker.check_equivalence(multi_module, "module top(); endmodule")

def test_equiv_mocked_equivalent(prepare_checker, monkeypatch):
    """
    Tests a scenario where the standard equivalence method immediately succeeds.
    """
    def mock_run(*args, **kwargs):
        class MockCompleted:
            returncode = 0
            stdout = "Equivalence successfully proven"
            stderr = ""
        return MockCompleted()

    monkeypatch.setattr("subprocess.run", mock_run)

    checker = prepare_checker
    checker.yosys_installed = True
    gold = "module top(); endmodule"
    ref = "module top(); endmodule"
    result = checker.check_equivalence(gold, ref)
    assert result is True
    assert checker.get_counterexample() is None

def test_equiv_mocked_not_equiv(prepare_checker, monkeypatch):
    """
    Tests a scenario where the standard equivalence method fails with an assert,
    proving non-equivalence.
    """
    def mock_run(*args, **kwargs):
        class MockCompleted:
            returncode = 1
            stdout = "Assert failed at line X"
            stderr = ""
        return MockCompleted()

    monkeypatch.setattr("subprocess.run", mock_run)

    checker = prepare_checker
    checker.yosys_installed = True
    gold = "module top(); assign x = 0; endmodule"
    ref  = "module top(); assign x = 1; endmodule"
    result = checker.check_equivalence(gold, ref)
    assert result is False
    assert "(Method: equiv)" in checker.get_counterexample()

def test_smt_fallback_inconclusive(prepare_checker, monkeypatch):
    """
    If the first method is inconclusive, check that we call the SMT approach.
    We'll mock two calls: the first returns an error, the second returns success.
    """
    calls = []

    def mock_run(*args, **kwargs):
        if len(calls) == 0:
            # First call => unknown error => None
            calls.append("equiv-call")
            class MockErrorProc:
                returncode = 123
                stdout = "Some error not indicating assert or sat"
                stderr = ""
            return MockErrorProc()
        else:
            # Second call => success => equivalent
            calls.append("smt-call")
            class MockSmtProc:
                returncode = 0
                stdout = "Equivalence proven via SMT"
                stderr = ""
            return MockSmtProc()

    monkeypatch.setattr("subprocess.run", mock_run)

    checker = prepare_checker
    checker.yosys_installed = True
    gold = "module top(); assign x = 1'b1; endmodule"
    ref  = "module top(); assign x = 1'b1; endmodule"

    result = checker.check_equivalence(gold, ref)
    assert len(calls) == 2  # both calls (equiv + smt) were tried
    assert result is True
    # assert checker.get_error() == ""  # no final error stored

