import os
import pytest
import subprocess
import uuid
import datetime
from pathlib import Path
from hagent.tool.equiv_check import Equiv_check


@pytest.fixture
def prepare_checker():
    """
    Fixture to instantiate the checker and ensure a clean workspace before each test.
    """
    # Create unique directory for test
    test_id = f'{datetime.datetime.now().strftime("%Y%m%d_%H%M%S")}_{uuid.uuid4().hex[:8]}'
    test_dir = Path('output') / 'equiv_check' / test_id
    test_dir.mkdir(parents=True, exist_ok=True)

    # Change to test directory for the test
    original_cwd = os.getcwd()
    os.chdir(test_dir)

    checker = Equiv_check()

    yield checker

    # Change back to original directory
    os.chdir(original_cwd)


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
    monkeypatch.setattr('hagent.tool.equiv_check.Equiv_check.setup_docker_fallback', mock_docker_fallback)

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
    monkeypatch.setattr('hagent.tool.equiv_check.Equiv_check.setup_docker_fallback', mock_docker_fallback)

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


def test_multiple_modules(prepare_checker, monkeypatch):
    """
    Multiple modules in gold should be matched with compatible modules in gate.
    Each gold module should find a matching gate module with compatible IOs.
    """
    checker = prepare_checker
    checker.yosys_installed = True

    # Gold design with two modules
    gold_multi_module = """
module m1(input a, output b);
  assign b = a;
endmodule

module m2(input x, output y);
  assign y = x;
endmodule
"""

    # Gate design with three modules (two match gold, one extra)
    gate_multi_module = """
module n1(input a, output b);
  assign b = a;
endmodule

module n2(input x, output y);
  assign y = x;
endmodule

module n3(input z, output w);
  assign w = ~z;
endmodule
"""

    # Mock successful Yosys runs for both module pairs
    def mock_run(*args, **kwargs):
        class MockCompleted:
            returncode = 0
            stdout = 'Equivalence proven'
            stderr = ''

        return MockCompleted()

    monkeypatch.setattr('subprocess.run', mock_run)

    # Should succeed - both gold modules find matching gate modules
    result = checker.check_equivalence(gold_multi_module, gate_multi_module)
    assert result is True


def test_multiple_modules_no_match(prepare_checker):
    """
    When some gold modules can't find matching gate modules, ValueError should be raised.
    """
    checker = prepare_checker
    checker.yosys_installed = True

    # Gold design with two modules
    gold_multi_module = """
module m1(input a, output b);
  assign b = a;
endmodule

module m2(input x, output y);
  assign y = x;
endmodule
"""

    # Gate design with only one matching module
    gate_single_module = """
module n1(input a, output b);
  assign b = a;
endmodule
"""

    # Should raise ValueError because m2 can't find a match
    with pytest.raises(ValueError, match='Some gold modules could not find matching gate modules'):
        checker.check_equivalence(gold_multi_module, gate_single_module)


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

    # Patch the extract_module_name method to avoid the hardcoded 'SingleCycleCPU'
    monkeypatch.setattr(prepare_checker, 'extract_module_name', lambda code, top_module=None: 'Top')

    checker = prepare_checker
    checker.yosys_installed = True
    gold = 'module Top(); endmodule'
    ref = 'module Top(); endmodule'
    result = checker.check_equivalence(gold, ref)
    assert result is True
    assert checker.get_counterexample() is None


def test_equiv_mocked_not_equiv(prepare_checker, monkeypatch):
    """
    Tests a scenario where the SMT method finds designs are not equivalent,
    proving non-equivalence.
    """

    def mock_run(*args, **kwargs):
        class MockCompleted:
            returncode = 0
            stdout = 'SAT #10 FAIL at line X'
            stderr = ''

        return MockCompleted()

    monkeypatch.setattr('subprocess.run', mock_run)

    # Patch the extract_module_name method to avoid the hardcoded 'SingleCycleCPU'
    monkeypatch.setattr(prepare_checker, 'extract_module_name', lambda code, top_module=None: 'Top')

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

    # Patch the extract_module_name method to avoid the hardcoded 'SingleCycleCPU'
    monkeypatch.setattr(prepare_checker, 'extract_module_name', lambda code, top_module=None: 'Top')

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

    # Patch the extract_module_name method to avoid the hardcoded 'SingleCycleCPU'
    monkeypatch.setattr(prepare_checker, 'extract_module_name', lambda code, top_module=None: 'Top')

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

    # Patch the extract_module_name method to avoid the hardcoded 'SingleCycleCPU'
    monkeypatch.setattr(prepare_checker, 'extract_module_name', lambda code, top_module=None: 'Top')

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

    # Patch the extract_module_name method to avoid the hardcoded 'SingleCycleCPU'
    monkeypatch.setattr(prepare_checker, 'extract_module_name', lambda code, top_module=None: 'Top')

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

    test_id = f'{datetime.datetime.now().strftime("%Y%m%d_%H%M%S")}_{uuid.uuid4().hex[:8]}'
    test_dir = Path('output') / 'equiv_check_command_test' / test_id
    test_dir.mkdir(parents=True, exist_ok=True)
    tmp_name = test_dir / 'test_command.ys'
    tmp_name.write_text('test command')

    checker = prepare_checker
    code, out, err = checker.run_yosys_command(str(tmp_name))
    assert code == 1
    assert out == ''
    assert 'Test exception' in err
    assert 'Test exception' in checker.error_message


def test_run_yosys_command_timeout(prepare_checker, monkeypatch):
    """
    Tests _run_yosys_command when a timeout occurs.
    """

    def mock_run(*args, **kwargs):
        raise subprocess.TimeoutExpired(cmd='yosys', timeout=60)

    monkeypatch.setattr('subprocess.run', mock_run)

    test_id = f'{datetime.datetime.now().strftime("%Y%m%d_%H%M%S")}_{uuid.uuid4().hex[:8]}'
    test_dir = Path('output') / 'equiv_check_timeout_test' / test_id
    test_dir.mkdir(parents=True, exist_ok=True)
    tmp_name = test_dir / 'test_command.ys'
    tmp_name.write_text('test command')

    checker = prepare_checker
    code, out, err = checker.run_yosys_command(str(tmp_name))
    assert code == 1
    assert out == ''
    assert 'timeout' in err.lower()
    assert 'timeout' in checker.error_message.lower()


def test_analyze_yosys_result_unknown(prepare_checker):
    """
    Tests analyze_yosys_result with an unknown method.
    """
    checker = prepare_checker
    result = checker.analyze_yosys_result(1, '', '', 'unknown_method')
    assert result is None
    assert 'Yosys returned code 1' in checker.error_message


def test_write_temp_verilog(prepare_checker):
    """
    Tests the write_temp_verilog method.
    """
    checker = prepare_checker

    test_id = f'{datetime.datetime.now().strftime("%Y%m%d_%H%M%S")}_{uuid.uuid4().hex[:8]}'
    work_dir = Path('output') / 'equiv_check_verilog_test' / test_id
    work_dir.mkdir(parents=True, exist_ok=True)

    # Test writing Verilog code to a file
    verilog_code = 'module Test(); endmodule'
    filename = checker.write_temp_verilog(str(work_dir), verilog_code, 'test')

    assert os.path.exists(filename)
    with open(filename, 'r') as f:
        content = f.read()
    assert content == verilog_code


def test_analyze_yosys_result_smt_with_sat(prepare_checker):
    """
    Tests analyze_yosys_result with SMT method and SAT result.
    """
    checker = prepare_checker

    # Test with SMT method and SAT result (not equivalent)
    result = checker.analyze_yosys_result(0, 'SAT #10 FAIL', '', 'smt')
    assert result is False

    # Test with SMT method and no SAT/FAIL (equivalent)
    result = checker.analyze_yosys_result(0, 'No SAT or FAIL here', '', 'smt')
    assert result is True


def test_extract_module_name_no_modules(prepare_checker):
    """
    Tests _extract_module_name with no modules.
    """
    checker = prepare_checker

    # Test with no modules
    with pytest.raises(ValueError, match="No 'module' definition found"):
        checker.extract_module_name('// Just a comment, no modules.')

    # Test with multiple modules and no top module specified
    multi_module = """
    module m1();
    endmodule

    module m2();
    endmodule
    """
    with pytest.raises(ValueError, match='Multiple modules found'):
        checker.extract_module_name(multi_module)

    # Test with a single module
    single_module = 'module test(); endmodule'
    result = checker.extract_module_name(single_module)
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
    result = checker.extract_module_name(multi_module, top_module='top_module')
    assert result == 'top_module'


def test_counterexample_with_signal_table(prepare_checker, monkeypatch):
    """
    Tests that get_counterexample returns the signal table when designs are not equivalent.
    This test simulates the case where simple_test changes from 'assign y = a' to 'assign y = !a'.
    """
    # Mock Yosys output that includes the counterexample signal table
    # fmt: off
    yosys_output_with_counterexample = (
        "[base case 1] Solving problem with 103 variables and 262 clauses..\n"
        "SAT temporal induction proof finished - model found for base case: FAIL!\n"
        "\n"
        "   ______                   ___       ___       _ _            _ _\n"
        r"  (_____ \                 / __)     / __)     (_) |          | | |" + "\n"
        r"   _____) )___ ___   ___ _| |__    _| |__ _____ _| | _____  __| | |" + "\n"
        r"  |  ____/ ___) _ \ / _ (_   __)  (_   __|____ | | || ___ |/ _  |_|" + "\n"
        r"  | |   | |  | |_| | |_| || |       | |  / ___ | | || ____( (_| |_" + "\n"
        r"  |_|   |_|   \___/ \___/ |_|       |_|  \_____|_|\_)_____)\____|_|" + "\n"
        "\n"
        "\n"
        "  Time Signal Name             Dec       Hex           Bin\n"
        "  ---- --------------- ----------- --------- -------------\n"
        r"     1 \gate_y                   1         1             1" + "\n"
        r"     1 \gold_y                   0         0             0" + "\n"
        r"     1 \in_a                     1         1             1" + "\n"
        r"     1 \trigger                  1         1             1" + "\n"
        "\n"
        "End of script. Logfile hash: 4e4c2a3c22, CPU: user 0.02s system 0.00s, MEM: 13.39 MB peak\n"
        "Yosys 0.56 (git sha1 9c447ad9d4b1ea589369364eea38b4d70da2c599, clang++ 17.0.0 -fPIC -O3)\n"
    )
    # fmt: on

    def mock_run(*args, **kwargs):
        class MockCompleted:
            returncode = 0
            stdout = yosys_output_with_counterexample
            stderr = ''

        return MockCompleted()

    monkeypatch.setattr('subprocess.run', mock_run)
    monkeypatch.setattr(prepare_checker, 'extract_module_name', lambda code, top_module=None: 'simple_test')

    checker = prepare_checker
    checker.yosys_installed = True

    # Define the two different versions of simple_test
    gold_code = """
module simple_test(
  input  wire a,
  output wire y
);
  assign y = a;
endmodule
"""

    gate_code = """
module simple_test(
  input  wire a,
  output wire y
);
  assign y = !a;
endmodule
"""

    # Check equivalence - should return False since designs differ
    result = checker.check_equivalence(gold_code, gate_code, 'simple_test')
    assert result is False

    # Get the counterexample
    counterexample = checker.get_counterexample()

    # The counterexample should contain the signal table
    assert counterexample is not None
    assert 'Time Signal Name' in counterexample
    assert '\\gate_y' in counterexample
    assert '\\gold_y' in counterexample
    assert '\\in_a' in counterexample
    assert '\\trigger' in counterexample


def test_counterexample_parsing_signal_table(prepare_checker):
    """
    Tests the parsing of signal table from Yosys output for counterexample extraction.
    """
    checker = prepare_checker

    # Sample Yosys output with signal table
    # fmt: off
    stdout_with_table = (
        "[base case 1] Solving problem with 103 variables and 262 clauses..\n"
        "SAT temporal induction proof finished - model found for base case: FAIL!\n"
        "\n"
        "  Time Signal Name             Dec       Hex           Bin\n"
        "  ---- --------------- ----------- --------- -------------\n"
        r"     1 \gate_y                   1         1             1" + "\n"
        r"     1 \gold_y                   0         0             0" + "\n"
        r"     1 \in_a                     1         1             1" + "\n"
        r"     1 \trigger                  1         1             1" + "\n"
        "\n"
        "End of script. Logfile hash: 4e4c2a3c22\n"
    )
    # fmt: on

    stderr = ''

    # Test that the signal table can be parsed from this output
    signal_table = checker.parse_signal_table(stdout_with_table, stderr)

    # Verify that the signal table was extracted successfully
    assert signal_table is not None
    assert 'Time Signal Name' in signal_table
    assert '\\gate_y' in signal_table
    assert '\\gold_y' in signal_table


if __name__ == '__main__':
    pytest.main(['-v', '-s', '--tb=long', __file__])
