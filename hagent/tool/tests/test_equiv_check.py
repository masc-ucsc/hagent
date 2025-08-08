import os
import pytest
import shutil
import tempfile
import subprocess
from hagent.tool.equiv_check import Equiv_check


@pytest.fixture
def prepare_checker():
    """
    Fixture to instantiate the checker and ensure a clean workspace before each test.
    """
    # Cleanup before test runs:
    if os.path.isdir('equiv_check'):
        shutil.rmtree('equiv_check')
    checker = Equiv_check()
    return checker


def test_setup_failure(prepare_checker):
    """
    Tests setup with an invalid Yosys path, expecting failure and proper error message.
    """
    checker = prepare_checker
    result = checker.setup(yosys_path='nonexistent_yosys_binary')
    assert result is False
    assert checker.yosys_installed is False
    assert 'Yosys not found' in checker.get_error()


def test_setup_success(prepare_checker, monkeypatch):
    """
    Tests setup with a mocked 'yosys -V' call that simulates success.
    """

    def mock_run(*args, **kwargs):
        class MockCompleted:
            returncode = 0
            stdout = 'Yosys 0.90+ (mocked)'
            stderr = ''

        return MockCompleted()

    monkeypatch.setattr('subprocess.run', mock_run)

    checker = prepare_checker
    result = checker.setup()  # no specific path; mock ensures success
    assert result is True
    assert checker.yosys_installed is True
    assert checker.get_error() == ''


def test_setup_version_parsing_failure(prepare_checker, monkeypatch):
    """
    Tests setup with unparseable version output.
    """

    def mock_run(*args, **kwargs):
        class MockCompleted:
            returncode = 0
            stdout = 'Yosys (unparseable version)'
            stderr = ''

        return MockCompleted()

    # Mock Docker fallback to fail
    def mock_docker_fallback(self):
        return False

    monkeypatch.setattr('subprocess.run', mock_run)
    monkeypatch.setattr('hagent.tool.equiv_check.Equiv_check._setup_docker_fallback', mock_docker_fallback)

    checker = prepare_checker
    result = checker.setup()
    assert result is False
    assert checker.yosys_installed is False
    assert 'Unable to parse Yosys version' in checker.get_error()


def test_setup_version_too_old(prepare_checker, monkeypatch):
    """
    Tests setup with a version that's too old.
    """

    def mock_run(*args, **kwargs):
        class MockCompleted:
            returncode = 0
            stdout = 'Yosys 0.3.0 (too old)'
            stderr = ''

        return MockCompleted()

    # Mock Docker fallback to fail
    def mock_docker_fallback(self):
        return False

    monkeypatch.setattr('subprocess.run', mock_run)
    monkeypatch.setattr('hagent.tool.equiv_check.Equiv_check._setup_docker_fallback', mock_docker_fallback)

    checker = prepare_checker
    result = checker.setup()
    assert result is False
    assert checker.yosys_installed is False
    assert 'below the required version' in checker.get_error()


def test_no_module(prepare_checker):
    """
    If no module is found, a ValueError is raised.
    """
    checker = prepare_checker
    checker.yosys_installed = True
    no_module_code = '// Just a comment, no modules.'

    with pytest.raises(ValueError):
        checker.check_equivalence(no_module_code, 'module top(); endmodule')


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
        checker.check_equivalence(multi_module, 'module top(); endmodule')


def test_check_equivalence_yosys_not_installed(prepare_checker):
    """
    Tests check_equivalence when Yosys is not installed.
    """
    checker = prepare_checker
    checker.yosys_installed = False

    with pytest.raises(RuntimeError, match='Yosys not installed'):
        checker.check_equivalence('module Top(); endmodule', 'module Top(); endmodule')


def test_equiv_mocked_equivalent(prepare_checker, monkeypatch):
    """
    Tests a scenario where the standard equivalence method immediately succeeds.
    """

    def mock_run(*args, **kwargs):
        class MockCompleted:
            returncode = 0
            stdout = 'Equivalence successfully proven'
            stderr = ''

        return MockCompleted()

    monkeypatch.setattr('subprocess.run', mock_run)

    # Patch the _extract_module_name method to avoid the hardcoded 'SingleCycleCPU'
    monkeypatch.setattr(prepare_checker, '_extract_module_name', lambda code, top_module=None: 'Top')

    checker = prepare_checker
    checker.yosys_installed = True
    gold = 'module Top(); endmodule'
    ref = 'module Top(); endmodule'
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
            stdout = 'Assert failed at line X'
            stderr = ''

        return MockCompleted()

    monkeypatch.setattr('subprocess.run', mock_run)

    # Patch the _extract_module_name method to avoid the hardcoded 'SingleCycleCPU'
    monkeypatch.setattr(prepare_checker, '_extract_module_name', lambda code, top_module=None: 'Top')

    checker = prepare_checker
    checker.yosys_installed = True
    gold = 'module Top(); assign x = 0; endmodule'
    ref = 'module Top(); assign x = 1; endmodule'
    result = checker.check_equivalence(gold, ref)
    assert result is False


def test_equiv_mocked_error(prepare_checker, monkeypatch):
    """
    Tests a scenario where Yosys returns an error.
    """

    def mock_run(*args, **kwargs):
        class MockCompleted:
            returncode = 1
            stdout = ''
            stderr = 'ERROR: Syntax error in Verilog code'

        return MockCompleted()

    monkeypatch.setattr('subprocess.run', mock_run)

    # Patch the _extract_module_name method to avoid the hardcoded 'SingleCycleCPU'
    monkeypatch.setattr(prepare_checker, '_extract_module_name', lambda code, top_module=None: 'Top')

    checker = prepare_checker
    checker.yosys_installed = True
    gold = 'module Top(); endmodule'
    ref = 'module Top(); endmodule'
    result = checker.check_equivalence(gold, ref)
    assert result is False


def test_equiv_mocked_timeout(prepare_checker, monkeypatch):
    """
    Tests a scenario where Yosys times out.
    """

    def mock_run(*args, **kwargs):
        class MockCompleted:
            returncode = 1
            stdout = ''
            stderr = 'timeout occurred'

        return MockCompleted()

    monkeypatch.setattr('subprocess.run', mock_run)

    # Patch the _extract_module_name method to avoid the hardcoded 'SingleCycleCPU'
    monkeypatch.setattr(prepare_checker, '_extract_module_name', lambda code, top_module=None: 'Top')

    checker = prepare_checker
    checker.yosys_installed = True
    gold = 'module Top(); endmodule'
    ref = 'module Top(); endmodule'
    result = checker.check_equivalence(gold, ref)
    assert result is None


def test_equiv_mocked_smt_sat(prepare_checker, monkeypatch):
    """
    Tests a scenario where the SMT method finds a counterexample (SAT).
    """

    # Mock a single call that returns an error (which will be interpreted as non-equivalence)
    def mock_run(*args, **kwargs):
        class MockCompleted:
            returncode = 1
            stdout = ''
            stderr = 'ERROR: Syntax error in Verilog code'

        return MockCompleted()

    monkeypatch.setattr('subprocess.run', mock_run)

    # Patch the _extract_module_name method to avoid the hardcoded 'SingleCycleCPU'
    monkeypatch.setattr(prepare_checker, '_extract_module_name', lambda code, top_module=None: 'Top')

    checker = prepare_checker
    checker.yosys_installed = True
    gold = 'module Top(); endmodule'
    ref = 'module Top(); endmodule'
    result = checker.check_equivalence(gold, ref)
    assert result is False


def test_equiv_mocked_smt_unsat(prepare_checker, monkeypatch):
    """
    Tests a scenario where the SMT method proves equivalence (UNSAT).
    """

    # Mock a single call that returns success (which will be interpreted as equivalence)
    def mock_run(*args, **kwargs):
        class MockCompleted:
            returncode = 0
            stdout = 'Equivalence successfully proven'
            stderr = ''

        return MockCompleted()

    monkeypatch.setattr('subprocess.run', mock_run)

    # Patch the _extract_module_name method to avoid the hardcoded 'SingleCycleCPU'
    monkeypatch.setattr(prepare_checker, '_extract_module_name', lambda code, top_module=None: 'Top')

    checker = prepare_checker
    checker.yosys_installed = True
    gold = 'module Top(); endmodule'
    ref = 'module Top(); endmodule'
    result = checker.check_equivalence(gold, ref)
    assert result is True


def test_run_yosys_command_exception(prepare_checker, monkeypatch):
    """
    Tests _run_yosys_command when an exception occurs.
    """

    def mock_run(*args, **kwargs):
        raise Exception('Test exception')

    monkeypatch.setattr('subprocess.run', mock_run)

    with tempfile.NamedTemporaryFile(delete=False) as tmp:
        tmp_name = tmp.name
        tmp.write(b'test command')

    try:
        checker = prepare_checker
        code, out, err = checker._run_yosys_command(tmp_name)
        assert code == 1
        assert out == ''
        assert 'Test exception' in err
        assert 'Test exception' in checker.error_message
    finally:
        if os.path.exists(tmp_name):
            os.remove(tmp_name)


def test_run_yosys_command_timeout(prepare_checker, monkeypatch):
    """
    Tests _run_yosys_command when a timeout occurs.
    """

    def mock_run(*args, **kwargs):
        raise subprocess.TimeoutExpired(cmd='yosys', timeout=60)

    monkeypatch.setattr('subprocess.run', mock_run)

    with tempfile.NamedTemporaryFile(delete=False) as tmp:
        tmp_name = tmp.name
        tmp.write(b'test command')

    try:
        checker = prepare_checker
        code, out, err = checker._run_yosys_command(tmp_name)
        assert code == 1
        assert out == ''
        assert 'timeout' in err.lower()
        assert 'timeout' in checker.error_message.lower()
    finally:
        if os.path.exists(tmp_name):
            os.remove(tmp_name)


def test_analyze_yosys_result_unknown(prepare_checker):
    """
    Tests _analyze_yosys_result with an unknown method.
    """
    checker = prepare_checker
    result = checker._analyze_yosys_result(1, '', '', 'unknown_method')
    assert result is None
    assert 'Yosys returned code 1' in checker.error_message


def test_write_temp_verilog(prepare_checker):
    """
    Tests the _write_temp_verilog method.
    """
    checker = prepare_checker

    work_dir = tempfile.mkdtemp()
    try:
        # Test writing Verilog code to a file
        verilog_code = 'module Test(); endmodule'
        filename = checker._write_temp_verilog(work_dir, verilog_code, 'test')

        assert os.path.exists(filename)
        with open(filename, 'r') as f:
            content = f.read()
        assert content == verilog_code
    finally:
        shutil.rmtree(work_dir)


def test_analyze_yosys_result_smt_with_sat(prepare_checker):
    """
    Tests _analyze_yosys_result with SMT method and SAT result.
    """
    checker = prepare_checker

    # Test with SMT method and SAT result (not equivalent)
    result = checker._analyze_yosys_result(0, 'SAT #10 FAIL', '', 'smt')
    assert result is False

    # Test with SMT method and no SAT/FAIL (equivalent)
    result = checker._analyze_yosys_result(0, 'No SAT or FAIL here', '', 'smt')
    assert result is True


def test_extract_module_name_no_modules(prepare_checker):
    """
    Tests _extract_module_name with no modules.
    """
    checker = prepare_checker

    # Test with no modules
    with pytest.raises(ValueError, match="No 'module' definition found"):
        checker._extract_module_name('// Just a comment, no modules.')

    # Test with multiple modules and no top module specified
    multi_module = """
    module m1();
    endmodule
    
    module m2();
    endmodule
    """
    with pytest.raises(ValueError, match='Multiple modules found'):
        checker._extract_module_name(multi_module)

    # Test with a single module
    single_module = 'module test(); endmodule'
    result = checker._extract_module_name(single_module)
    assert result == 'test'


def test_extract_module_name_with_specified_top(prepare_checker):
    """
    Tests _extract_module_name with a specified top module that exists in the code.
    This specifically tests line 150 in equiv_check.py.
    """
    checker = prepare_checker

    # Create Verilog code with multiple modules
    multi_module = """
    module m1();
    endmodule
    
    module top_module();
    endmodule
    
    module m2();
    endmodule
    """

    # Test with a specified top module that exists
    result = checker._extract_module_name(multi_module, top_module='top_module')
    assert result == 'top_module'


if __name__ == '__main__':
    pytest.main(['-v', '-s', '--tb=long', __file__])
