#!/usr/bin/env python3
import os
import tempfile
import pytest
from unittest.mock import patch, MagicMock
import difflib

from hagent.step.v2chisel_fix.v2chisel_fix import V2chisel_fix, diff_code

@pytest.fixture
def valid_input():
    # Create a minimal valid input dictionary for V2chisel_fix.
    return {
        "chisel_pass1": {
            "chisel_changed": "class MyModule extends Module { val io = IO(new Bundle {}) }",
            "chisel_subset": "class MyModule extends Module { val io = IO(new Bundle {}) }",
            "verilog_candidate": "module mymodule(); endmodule",
            "was_valid": True
        },
        # Provide a nonempty chisel_original so that refined code is not empty.
        "chisel_original": "class MyModule extends Module { val io = IO(new Bundle {}) }",
        "verilog_fixed": "module mymodule(); endmodule",
        "llm": {"model": "test-model"}
    }

@pytest.fixture
def step_instance(valid_input):
    step = V2chisel_fix()
    # Set a dummy output file so that write_output does not fail.
    step.set_io(inp_file="dummy_input.yaml", out_file="dummy_output.yaml")
    # Inject the input_data dictionary.
    step.input_data = valid_input
    return step

def test_run_initial_equiv_pass(step_instance):
    """
    Test when the initial equivalence check passes so no refinement is needed.
    """
    # Patch _check_equivalence to always return that the candidate is equivalent.
    with patch.object(step_instance, "_check_equivalence", return_value=(True, None)):
        result = step_instance.run(step_instance.input_data)
        assert result["chisel_fixed"]["equiv_passed"] is True
        # Expect that the refined chisel equals the original chisel (or chisel_changed)
        refined = result["chisel_fixed"]["refined_chisel"]
        assert "class MyModule" in refined

def test_run_with_react_refinement(step_instance):
    """
    Test when the equivalence check fails so the React cycle is used
    and it returns a refined candidate.
    """
    # Fake equivalence check: always fail.
    def fake_check_equivalence(gold, candidate):
        return (False, "Simulated LEC failure")
    # Fake chisel-to-verilog conversion: always succeed.
    def fake_run_chisel2v(code):
        return (True, "dummy verilog", "")
    with patch.object(step_instance, "_check_equivalence", side_effect=fake_check_equivalence), \
         patch.object(step_instance, "_run_chisel2v", side_effect=fake_run_chisel2v), \
         patch("hagent.tool.react.React") as MockReact:
        mock_react = MagicMock()
        mock_react.react_cycle.return_value = "refined MyModule code"
        MockReact.return_value = mock_react
        result = step_instance.run(step_instance.input_data)
        assert result["chisel_fixed"]["equiv_passed"] is True
        assert result["chisel_fixed"]["refined_chisel"] == "refined MyModule code"

def test_run_react_failure(step_instance):
    """
    Test that if React returns an empty string (i.e. refinement fails),
    the run() method raises an error.
    """
    with patch("hagent.tool.react.React") as MockReact:
        mock_react = MagicMock()
        # Simulate React cycle failure by returning an empty string.
        mock_react.react_cycle.return_value = ""
        MockReact.return_value = mock_react
        with pytest.raises(Exception, match="React failed to refine the code."):
            step_instance.run(step_instance.input_data)

def test_diff_code():
    text1 = "line1\nline2\nline3\n"
    text2 = "line1\nline2 modified\nline3\n"
    diff_output = diff_code(text1, text2)
    # Check that the diff contains indications of changes (lines starting with '-' and '+')
    assert '-' in diff_output and '+' in diff_output
    assert "line2 modified" in diff_output

def test_generate_diff():
    instance = V2chisel_fix()
    old_code = "line1\nline2\n"
    new_code = "line1\nline2 changed\n"
    generated_diff = instance._generate_diff(old_code, new_code)
    # Diff should start with headers for original and modified files
    assert generated_diff.startswith('--- Original version')
    assert '+++ Modified version' in generated_diff

def test_strip_markdown_fences():
    instance = V2chisel_fix()
    code_with_fences = "```python\ncode line\n```"
    stripped = instance._strip_markdown_fences(code_with_fences)
    assert '```' not in stripped
    assert stripped == "code line"

def test_find_chisel_classname():
    instance = V2chisel_fix()
    code = "class TestModule extends Module { val io = IO(new Bundle{}) }"
    classname = instance._find_chisel_classname(code)
    assert classname == "TestModule"

def test_run_chisel2v_empty():
    instance = V2chisel_fix()
    valid, verilog_out, err = instance._run_chisel2v("")
    assert valid is False
    assert err == 'Chisel snippet is empty'

def test_run_chisel2v_success(monkeypatch):
    instance = V2chisel_fix()
    fake_chisel2v = MagicMock()
    fake_chisel2v.setup.return_value = True
    fake_chisel2v.generate_verilog.return_value = "module test(...); endmodule"
    with patch('hagent.step.v2chisel_fix.v2chisel_fix.Chisel2v', return_value=fake_chisel2v):
        valid, ver_out, err = instance._run_chisel2v("non-empty chisel code")
        assert valid is True
        assert "module" in ver_out

def test_iterative_compile_fix(monkeypatch):
    instance = V2chisel_fix()
    instance.template_config = MagicMock(template_dict={"v2chisel_fix": {"prompt_compiler_fix": "dummy prompt"}})
    instance.refine_llm = MagicMock()
    instance.refine_llm.name = "v2chisel_fix"
    instance.chisel_original = "original code"
    # Setup refine_llm to return a dummy diff
    fake_diff = "--- dummy diff"
    instance.refine_llm.inference.return_value = [fake_diff]
    # Simulate chisel_extractor.parse returning the dummy diff
    instance.chisel_extractor = MagicMock()
    instance.chisel_extractor.parse.return_value = fake_diff
    # Force _run_chisel2v to succeed
    instance._run_chisel2v = lambda code: (True, "verilog", "")
    # Patch ChiselDiffApplier to append ' fixed' to the code
    fake_applier = MagicMock()
    fake_applier.apply_diff.side_effect = lambda diff, code: code + " fixed"
    with patch('hagent.step.v2chisel_fix.v2chisel_fix.ChiselDiffApplier', return_value=fake_applier):
        new_code = instance._iterative_compile_fix("original code", "error")
        assert "fixed" in new_code

def test_refine_chisel_code(monkeypatch):
    instance = V2chisel_fix()
    instance.template_config = MagicMock(template_dict={"v2chisel_fix": {"prompt3": "dummy prompt3"}})
    instance.refine_llm = MagicMock()
    instance.refine_llm.name = "v2chisel_fix"
    instance.chisel_original = "original chisel"
    instance.chisel_subset = "subset"
    instance.verilog_diff_str = "verilog diff"
    fake_answer = "dummy diff"
    instance.refine_llm.inference.return_value = [fake_answer]
    instance.chisel_extractor = MagicMock()
    instance.chisel_extractor.parse.return_value = fake_answer
    diff_returned = instance._refine_chisel_code("current code", "lec error", 1)
    assert diff_returned == fake_answer

def test_refine_chisel_code_with_prompt4(monkeypatch):
    instance = V2chisel_fix()
    instance.template_config = MagicMock(template_dict={"v2chisel_fix": {"prompt4": "dummy prompt4", "prompt4_alternative": "dummy prompt4 alt"}})
    instance.refine_llm = MagicMock()
    instance.refine_llm.name = "v2chisel_fix"
    instance.chisel_original = "original chisel"
    instance.chisel_subset = "subset"
    instance.verilog_diff_str = "verilog diff"
    fake_answer = "candidate diff"
    instance.refine_llm.inference.return_value = [fake_answer]
    instance.chisel_extractor = MagicMock()
    instance.chisel_extractor.parse.side_effect = lambda x: x if "diff" in x else ""
    # Patch V2Chisel_pass1 to return non-empty hints
    fake_v2_pass1 = MagicMock()
    fake_v2_pass1._extract_chisel_subset.return_value = "new hints"
    with patch('hagent.step.v2chisel_fix.v2chisel_fix.V2Chisel_pass1', return_value=fake_v2_pass1):
        fake_applier = MagicMock()
        fake_applier.apply_diff.side_effect = lambda diff, code: code + " applied"
        with patch('hagent.step.v2chisel_fix.v2chisel_fix.ChiselDiffApplier', return_value=fake_applier):
            # In candidate evaluation, simulate failure for 'another diff' and success for fake_answer
            instance._run_chisel2v = lambda code: (False, "", "error") if "another" in code else (True, "verilog", "")
            diff_out = instance._refine_chisel_code_with_prompt4("current code", "lec error", 3)
            assert diff_out == fake_answer

def test_check_equivalence_success(monkeypatch):
    instance = V2chisel_fix()
    fake_equiv = MagicMock()
    fake_equiv.setup.return_value = True
    fake_equiv.check_equivalence.return_value = True
    with patch('hagent.step.v2chisel_fix.v2chisel_fix.Equiv_check', return_value=fake_equiv):
        equiv, error = instance._check_equivalence('gold', 'gate')
        assert equiv is True
        assert error is None

def test_check_equivalence_fail(monkeypatch):
    instance = V2chisel_fix()
    fake_equiv = MagicMock()
    fake_equiv.setup.return_value = True
    fake_equiv.check_equivalence.return_value = False
    fake_equiv.get_error.return_value = "error message"
    fake_equiv.get_counterexample.return_value = "counterexample info"
    with patch('hagent.step.v2chisel_fix.v2chisel_fix.Equiv_check', return_value=fake_equiv):
        equiv, error = instance._check_equivalence('gold', 'gate')
        assert equiv is False
        assert error == "counterexample info"

def test_check_equivalence_exception(monkeypatch):
    instance = V2chisel_fix()
    fake_equiv = MagicMock()
    fake_equiv.setup.return_value = True
    fake_equiv.check_equivalence.side_effect = Exception("boom")
    with patch('hagent.step.v2chisel_fix.v2chisel_fix.Equiv_check', return_value=fake_equiv):
        equiv, error = instance._check_equivalence('gold', 'gate')
        assert equiv is False
        assert "boom" in error

def test_check_candidate_with_compiler_success(monkeypatch):
    instance = V2chisel_fix()
    fake_compiler = MagicMock()
    fake_compiler.setup.return_value = True
    fake_compiler.add_inline.return_value = True
    fake_compiler.get_errors.return_value = []
    with patch('hagent.step.v2chisel_fix.v2chisel_fix.Compile_slang', return_value=fake_compiler):
        valid, msg = instance._check_candidate_with_compiler("verilog code")
        assert valid is True

def test_check_candidate_with_compiler_failure(monkeypatch):
    instance = V2chisel_fix()
    fake_compiler = MagicMock()
    fake_compiler.setup.return_value = True
    fake_compiler.add_inline.return_value = True
    fake_err = MagicMock()
    fake_err.msg = "compile error"
    fake_compiler.get_errors.return_value = [fake_err]
    with patch('hagent.step.v2chisel_fix.v2chisel_fix.Compile_slang', return_value=fake_compiler):
        valid, msg = instance._check_candidate_with_compiler("verilog code")
        assert valid is False
        assert "compile error" in msg

def test_setup_missing_chisel_pass1(monkeypatch):
    instance = V2chisel_fix()
    instance.set_io("dummy_input.yaml", "dummy_output.yaml")
    instance.read_input = lambda: {}
    # Override write_output and error to avoid file I/O and to raise exceptions
    instance.write_output = lambda data: None
    instance.error = lambda msg: (_ for _ in ()).throw(Exception(msg))
    # Set input_data without 'chisel_pass1' to trigger the error.
    instance.input_data = {}
    with pytest.raises(Exception, match="Missing 'chisel_pass1' in input YAML"):
        instance.setup()
