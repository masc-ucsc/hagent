# hagent/step/v2chisel_fix/tests/test_v2chisel_fix.py

import os
import pytest
from unittest.mock import patch, MagicMock

from hagent.step.v2chisel_fix.v2chisel_fix import V2ChiselFix


@pytest.fixture
def valid_input_file(tmp_path):
    """
    Creates a minimal valid YAML for V2ChiselFix:
      - 'chisel_pass1' with some snippet
      - 'verilog_fixed'
      - 'llm' if needed
    """
    content = """\
chisel_pass1:
  chisel_changed: |
    class MyModule extends Module {
      val io = IO(new Bundle {})
    }
  verilog_candidate: |
    module mymodule (input clk, rst);
    endmodule
  was_valid: true

verilog_fixed: |
  module mymodule (input clk, rst);
  // new changes
  endmodule

llm:
  model: "test-model"
"""
    fpath = tmp_path / "input_fix.yaml"
    fpath.write_text(content)
    return str(fpath)


@pytest.fixture
def step_with_io(valid_input_file, tmp_path):
    """
    Returns a V2ChiselFix step with an input path and a temp output.
    We'll call .setup() and .step() as needed in each test.
    """
    step_obj = V2ChiselFix()
    out_file = str(tmp_path / "output_fix.yaml")
    step_obj.set_io(inp_file=valid_input_file, out_file=out_file)
    return step_obj


def test_missing_chisel_pass1(tmp_path):
    """
    If 'chisel_pass1' isn't in the YAML => raises ValueError
    """
    content = """\
verilog_fixed: |
  module foo();
  endmodule
llm:
  model: test-model
"""
    bad_file = tmp_path / "input_bad.yaml"
    bad_file.write_text(content)

    step_obj = V2ChiselFix()
    out_file = tmp_path / "output_bad.yaml"
    step_obj.set_io(inp_file=str(bad_file), out_file=str(out_file))

    with pytest.raises(ValueError, match="Missing 'chisel_pass1' in input YAML"):
        step_obj.setup()


def test_no_prompt3_file(step_with_io):
    """
    If prompt3.yaml doesn't exist => prints a warning, refine_llm=None
    We do a normal run => no refine, but code is valid => no attempts
    """
    # Ensure there's NO prompt3.yaml in the directory
    step_dir = os.path.dirname(__file__)
    prompt3_path = os.path.join(step_dir, "prompt3.yaml")
    if os.path.exists(prompt3_path):
        os.remove(prompt3_path)

    step_with_io.setup()
    with patch("hagent.step.v2chisel_fix.v2chisel_fix.Equiv_check") as mock_eq:
        mock_eq_instance = MagicMock()
        mock_eq.return_value = mock_eq_instance
        # Let equivalence pass => no refine needed
        mock_eq_instance.setup.return_value = True
        mock_eq_instance.check_equivalence.return_value = True

        res = step_with_io.step()

    # verify 'chisel_fixed' in output
    assert "chisel_fixed" in res
    cf = res["chisel_fixed"]
    assert cf["equiv_passed"] is True
    # since code was equivalent, no refinement needed => refined_chisel = original
    assert cf["refined_chisel"].strip().startswith("class MyModule")

    # Cleanup
    if os.path.exists(prompt3_path):
        os.remove(prompt3_path)


def test_prompt3_but_no_llm_config(tmp_path):
    """
    If prompt3.yaml exists but there's no 'llm' config => print warn, refine_llm=None
    We do a normal run => no refine possible.
    """
    # Create prompt3.yaml
    test_dir = os.path.dirname(__file__)
    prompt3_path = os.path.join(test_dir, "prompt3.yaml")
    prompt3_path_contents = """\
messages:
  - role: system
    content: "This is prompt3 for refinement."
"""
    with open(prompt3_path, "w") as f:
        f.write(prompt3_path_contents)

    # Create an input file with no 'llm' block
    content = """\
chisel_pass1:
  chisel_changed: |
    class MyModule extends Module { val io = IO(new Bundle {}) }
  verilog_candidate: |
    module mymodule();
    endmodule
  was_valid: true

verilog_fixed: |
  module mymodule();
  endmodule
"""
    bad_llm_file = tmp_path / "input_no_llm.yaml"
    bad_llm_file.write_text(content)

    step_obj = V2ChiselFix()
    out_file = tmp_path / "output_no_llm.yaml"
    step_obj.set_io(inp_file=str(bad_llm_file), out_file=str(out_file))

    # Now run
    step_obj.setup()
    # Force equivalence pass => no refine needed
    with patch("hagent.step.v2chisel_fix.v2chisel_fix.Equiv_check") as mock_eq:
        mock_eq_inst = MagicMock()
        mock_eq.return_value = mock_eq_inst
        mock_eq_inst.setup.return_value = True
        mock_eq_inst.check_equivalence.return_value = True

        step_obj.step()

    # Cleanup
    if os.path.exists(prompt3_path):
        os.remove(prompt3_path)

def test_already_equiv_no_refine(step_with_io):
    """
    - LEC passes initially => no refine
    - check final output => 'equiv_passed': True, no iteration done
    """
    step_with_io.setup()
    with patch("hagent.step.v2chisel_fix.v2chisel_fix.Equiv_check") as mock_eq:
        mock_eq_inst = MagicMock()
        mock_eq.return_value = mock_eq_inst
        mock_eq_inst.setup.return_value = True
        mock_eq_inst.check_equivalence.return_value = True  # Already equiv => no refine

        res = step_with_io.step()

    cf = res["chisel_fixed"]
    assert cf["equiv_passed"] is True
    assert "class MyModule" in cf["refined_chisel"]

def test_lec_fails_refine_succeeds(step_with_io, tmp_path):
    """
    - LEC fails at first, we refine => new snippet => verilog => success
    """
    import hagent.step.v2chisel_fix.v2chisel_fix as fix_mod
    module_dir = os.path.dirname(os.path.abspath(fix_mod.__file__))
    prompt3_path = os.path.join(module_dir, "prompt3.yaml")

    # Write a valid prompt3.yaml (top-level list)
    with open(prompt3_path, "w") as pf:
        pf.write("""\
- role: system
  content: "Refinement system message"
""")

    try:
        step_with_io.setup()

        mock_eq_inst = MagicMock()
        mock_eq_inst.setup.return_value = True
        # LEC fails on first check, passes on second
        mock_eq_inst.check_equivalence.side_effect = [False, True]

        def mock_chat_side_effect(prompt_dict):
            code_in = prompt_dict["chisel_code"]
            # On first refinement => replace "MyModule" => "MyModule_attempt1"
            if "attempt1" not in code_in:
                return "```chisel\nclass MyModule_attempt1 extends Module {}\n```"
            return code_in  # no further change

        def mock_generate_verilog(chisel_code, module_name):
            # If code has "attempt1" => produce refined verilog
            if "attempt1" in chisel_code:
                return ("module refined_attempt1(); endmodule", None)
            return ("module original(); endmodule", None)

        with patch("hagent.core.step.yaml.dump", return_value=None), \
             patch("hagent.step.v2chisel_fix.v2chisel_fix.Equiv_check", return_value=mock_eq_inst), \
             patch.object(step_with_io, "_generate_verilog", side_effect=mock_generate_verilog), \
             patch.object(step_with_io.refine_llm, "chat", side_effect=mock_chat_side_effect):

            res = step_with_io.step()

        # Check final result => must have succeeded on second attempt
        cf = res["chisel_fixed"]
        assert cf["equiv_passed"] is True, "Expected success after second equivalence check"
        assert "MyModule_attempt1" in cf["refined_chisel"]
    finally:
        if os.path.exists(prompt3_path):
            os.remove(prompt3_path)




def test_lec_fails_all_attempts(step_with_io, tmp_path):
    """
    - LEC fails for all attempts, code changes each time
    - after lec_limit => final result equiv_passed=False
    """
    import hagent.step.v2chisel_fix.v2chisel_fix as fix_mod
    module_dir = os.path.dirname(os.path.abspath(fix_mod.__file__))
    prompt3_path = os.path.join(module_dir, "prompt3.yaml")

    with open(prompt3_path, "w") as f:
        f.write("""\
- role: system
  content: "Refine"
""")

    try:
        step_with_io.setup()
        step_with_io.lec_limit = 2  # shorten attempts

        mock_eq_inst = MagicMock()
        mock_eq_inst.setup.return_value = True
        mock_eq_inst.check_equivalence.return_value = False  # always fails

        def mock_chat_side_effect(prompt_dict):
            # Append X => code changes each attempt
            code_in = prompt_dict["chisel_code"]
            return "```chisel\n" + code_in + "X\n```"

        def mock_gen_verilog(chisel_code, module_name):
            return ("module changed(); endmodule", None)

        with patch("hagent.core.step.yaml.dump", return_value=None), \
             patch("hagent.step.v2chisel_fix.v2chisel_fix.Equiv_check", return_value=mock_eq_inst), \
             patch.object(step_with_io.refine_llm, "chat", side_effect=mock_chat_side_effect), \
             patch.object(step_with_io, "_generate_verilog", side_effect=mock_gen_verilog):

            res = step_with_io.step()

        cf = res["chisel_fixed"]
        assert cf["equiv_passed"] is False, "Should remain false after max attempts"
        # code changed each iteration => ends with "XX"
        assert cf["refined_chisel"].endswith("XX")
    finally:
        if os.path.exists(prompt3_path):
            os.remove(prompt3_path)




def test_lec_fails_refine_cannot_improve(step_with_io, tmp_path):
    """
    - LEC fails, LLM returns the same code => break out => final 'equiv_passed' False
    """
    import hagent.step.v2chisel_fix.v2chisel_fix as fix_mod
    module_dir = os.path.dirname(os.path.abspath(fix_mod.__file__))
    prompt3_path = os.path.join(module_dir, "prompt3.yaml")

    with open(prompt3_path, "w") as f:
        f.write("""\
- role: system
  content: "Refinement prompt"
""")

    try:
        step_with_io.setup()

        mock_eq_inst = MagicMock()
        mock_eq_inst.setup.return_value = True
        mock_eq_inst.check_equivalence.return_value = False  # fails

        def mock_chat_side_effect(prompt_dict):
            # Return the same code => no improvement => break
            return prompt_dict["chisel_code"]

        with patch("hagent.step.v2chisel_fix.v2chisel_fix.Equiv_check", return_value=mock_eq_inst), \
             patch.object(step_with_io.refine_llm, "chat", side_effect=mock_chat_side_effect), \
             patch.object(step_with_io, "_generate_verilog", return_value=("module x(); endmodule", None)):

            res = step_with_io.step()

        cf = res["chisel_fixed"]
        assert cf["equiv_passed"] is False
    finally:
        if os.path.exists(prompt3_path):
            os.remove(prompt3_path)



def test_refine_llm_not_present(step_with_io):
    """
    - If there's no prompt3.yaml => refine_llm = None => skip refinement.
    - But let's say LEC fails => we can't refine => final => fail
    """
    step_dir = os.path.dirname(__file__)
    prompt3_path = os.path.join(step_dir, "prompt3.yaml")
    if os.path.exists(prompt3_path):
        os.remove(prompt3_path)

    step_with_io.setup()

    mock_eq_inst = MagicMock()
    mock_eq_inst.setup.return_value = True
    mock_eq_inst.check_equivalence.return_value = False  # fails

    with patch("hagent.step.v2chisel_fix.v2chisel_fix.Equiv_check", return_value=mock_eq_inst):
        res = step_with_io.step()

    assert res["chisel_fixed"]["equiv_passed"] is False


def test_generate_verilog_missing_module(step_with_io):
    """
    test _generate_verilog => no 'module' substring => error
    """
    step_with_io.setup()
    # Patch the '_generate_verilog' method on the V2ChiselFix class
    with patch("hagent.step.v2chisel_fix.v2chisel_fix.V2ChiselFix._generate_verilog", return_value=(None, "missing 'module' keyword")):
        bad_out, bad_err = step_with_io._generate_verilog("some code", "shared_dir")
        assert bad_out is None
        assert "missing 'module' keyword" in bad_err



def test_generate_verilog_exception(step_with_io):
    """
    test _generate_verilog => exception in c2v.generate_verilog => catch => (None, error)
    """
    step_with_io.setup()

    with patch("hagent.step.v2chisel_fix.v2chisel_fix.Chisel2v.setup", return_value=True), \
         patch("hagent.step.v2chisel_fix.v2chisel_fix.Chisel2v.generate_verilog",
               side_effect=RuntimeError("some c2v error")):
        out, err = step_with_io._generate_verilog("class MyModule extends Module{}", "shared")
        assert out is None
        assert "some c2v error" in err


def test_check_equivalence_ok(step_with_io):
    """
    test _check_equivalence => eq == True
    """
    step_with_io.setup()

    # mock Equiv_check => True
    with patch("hagent.step.v2chisel_fix.v2chisel_fix.Equiv_check") as meq:
        eqinst = MagicMock()
        meq.return_value = eqinst
        eqinst.setup.return_value = True
        eqinst.check_equivalence.return_value = True

        iseq, lec_err = step_with_io._check_equivalence("module gold(); endmodule", "module ref(); endmodule")
        assert iseq is True
        assert lec_err is None


def test_check_equivalence_false(step_with_io):
    """
    test _check_equivalence => eq == False => get cex
    """
    step_with_io.setup()
    with patch("hagent.step.v2chisel_fix.v2chisel_fix.Equiv_check") as meq:
        eqinst = MagicMock()
        meq.return_value = eqinst
        eqinst.setup.return_value = True
        eqinst.check_equivalence.return_value = False
        eqinst.get_counterexample.return_value = "Counterexample found"

        iseq, lec_err = step_with_io._check_equivalence("module gold(); endmodule", "module ref(); endmodule")
        assert iseq is False
        assert "Counterexample found" in lec_err


def test_check_equivalence_none_result(step_with_io):
    """
    test _check_equivalence => eq == None => eqinst.get_error => 'some error'
    """
    step_with_io.setup()
    with patch("hagent.step.v2chisel_fix.v2chisel_fix.Equiv_check") as meq:
        eqinst = MagicMock()
        meq.return_value = eqinst
        eqinst.setup.return_value = True
        eqinst.check_equivalence.return_value = None
        eqinst.get_error.return_value = "LEC result is None"

        iseq, lec_err = step_with_io._check_equivalence("module gold();", "module ref();")
        assert iseq is False
        assert "LEC result is None" in lec_err


def test_check_equivalence_exception(step_with_io):
    """
    test _check_equivalence => exception => (False, str(e))
    """
    step_with_io.setup()
    with patch("hagent.step.v2chisel_fix.v2chisel_fix.Equiv_check") as meq:
        eqinst = MagicMock()
        meq.return_value = eqinst
        eqinst.setup.return_value = True
        eqinst.check_equivalence.side_effect = RuntimeError("Oops LEC")

        iseq, lec_err = step_with_io._check_equivalence("module gold();", "module ref();")
        assert iseq is False
        assert "Oops LEC" in lec_err


def test_check_equivalence_missing_code(step_with_io):
    """
    test _check_equivalence => missing gold or ref => immediate (False, 'Missing code...')
    """
    step_with_io.setup()
    iseq, lec_err = step_with_io._check_equivalence("", "module something();")
    assert iseq is False
    assert "Missing code" in lec_err


def test_refine_chisel_code_no_llm(step_with_io):
    """
    If refine_llm=None => _refine_chisel_code returns same code
    """
    step_with_io.setup()
    step_with_io.refine_llm = None

    new_code = step_with_io._refine_chisel_code("class MyModule extends Module{}", "some LEC error")
    assert "MyModule" in new_code  # same code returned


def test_refine_chisel_code_empty_response(step_with_io):
    """
    If LLM returns empty => keep old code
    """
    step_with_io.setup()
    # mock a refine_llm
    step_with_io.refine_llm = MagicMock()
    step_with_io.refine_llm.chat.return_value = "  "  # empty after strip

    old_code = "class MyModule extends Module {}"
    result = step_with_io._refine_chisel_code(old_code, "some error")
    assert result == old_code


def test_refine_chisel_code_no_fences(step_with_io):
    """
    If LLM returns triple backticks => they are stripped
    """
    step_with_io.setup()
    step_with_io.refine_llm = MagicMock()
    step_with_io.refine_llm.chat.return_value = """```chisel
class MyRefined extends Module {}
```"""

    old_code = "class MyModule extends Module {}"
    result = step_with_io._refine_chisel_code(old_code, "some error")
    assert "MyRefined" in result
    # triple backticks are removed
    assert "```" not in result


def test_generate_verilog_no_code(step_with_io):
    """
    If chisel_code is empty => (None, "No Chisel code...")
    """
    step_with_io.setup()
    out, err = step_with_io._generate_verilog("", "myshare")
    assert out is None
    assert "No Chisel code" in err


def test_find_chisel_classname(step_with_io):
    """
    check _find_chisel_classname => either found or fallback
    """
    step_with_io.setup()
    snippet1 = "class TopModule extends Module { }"
    name1 = step_with_io._find_chisel_classname(snippet1)
    assert name1 == "TopModule"

    snippet2 = "class something extends MultiIOModule {}"
    name2 = step_with_io._find_chisel_classname(snippet2)
    assert name2 == "MyModule"  # fallback => no 'extends Module' match

    snippet3 = ""
    name3 = step_with_io._find_chisel_classname(snippet3)
    assert name3 == "MyModule"


def test_strip_markdown_fences(step_with_io):
    """
    test removing triple backticks with optional language tags
    """
    step_with_io.setup()
    text = """```scala
class Foo extends Module {}
```"""
    out = step_with_io._strip_markdown_fences(text)
    assert "```" not in out
    assert "scala" not in out
    assert "class Foo extends Module" in out


def test_setup_no_prompt3_warning(tmp_path):
    """
    Test that a warning is printed when 'prompt3.yaml' is not found.
    Ensures that 'refine_llm' remains None.
    """
    # Create an input YAML with 'chisel_pass1' and 'llm'
    content = """\
chisel_pass1:
  chisel_changed: |
    class MyModule extends Module {
      val io = IO(new Bundle {})
    }
  verilog_candidate: |
    module mymodule();
    endmodule
  was_valid: true

verilog_fixed: |
  module mymodule();
  // new changes
  endmodule

llm:
  model: "test-model"
"""
    input_file = tmp_path / "input_no_prompt3.yaml"
    input_file.write_text(content)

    step_obj = V2ChiselFix()
    out_file = tmp_path / "output_no_prompt3.yaml"
    step_obj.set_io(inp_file=str(input_file), out_file=str(out_file))

    # Ensure 'prompt3.yaml' does not exist
    with patch("hagent.step.v2chisel_fix.v2chisel_fix.os.path.exists", return_value=False), \
         patch("builtins.print") as mock_print:
        step_obj.setup()

        # Verify that the warning was printed
        mock_print.assert_any_call('[WARN] prompt3.yaml not found, cannot refine if LEC fails.')
        assert step_obj.refine_llm is None


def test_run_missing_verilog_fixed(step_with_io, tmp_path):
    """
    Test that a warning is printed and LEC is skipped when 'verilog_fixed' is missing.
    """
    # Prepare input data without 'verilog_fixed'
    input_data = {
        "chisel_pass1": {
            "chisel_changed": "class MyModule extends Module { val io = IO(new Bundle {}) }",
            "verilog_candidate": "module mymodule(); endmodule",
            "was_valid": True
        },
        # 'verilog_fixed' is missing
        "llm": {
            "model": "test-model"
        }
    }

    # Mock Equiv_check to ensure it's not called
    with patch("hagent.step.v2chisel_fix.v2chisel_fix.Equiv_check") as mock_eq, \
         patch("builtins.print") as mock_print:
        step_with_io.setup()
        res = step_with_io.run(input_data)

        # Verify warning was printed
        mock_print.assert_any_call("[WARN] No 'verilog_fixed' in input. Skipping initial LEC check.")

        # Verify 'chisel_fixed' reflects the skipped LEC
        assert "chisel_fixed" in res
        cf = res["chisel_fixed"]
        assert cf["equiv_passed"] is False
        assert cf["refined_chisel"] == "class MyModule extends Module { val io = IO(new Bundle {}) }"
        assert cf.get("verilog_candidate") is None


        # Ensure Equiv_check was not called
        mock_eq.assert_not_called()


def test_run_equiv_check_setup_failure(step_with_io):
    """
    Test that an error is printed and equivalence check fails when Equiv_check.setup() fails.
    """
    # Import the module to determine the path for 'prompt3.yaml' (if needed)
    import hagent.step.v2chisel_fix.v2chisel_fix as v2chisel_fix_module

    module_dir = os.path.dirname(os.path.abspath(v2chisel_fix_module.__file__))
    prompt3_path = os.path.join(module_dir, "prompt3.yaml")

    # Ensure 'prompt3.yaml' is present to initialize refine_llm, but it will not be used since LEC fails
    with open(prompt3_path, "w") as f:
        f.write("""
  - role: system
    content: "Refinement system message"
""")

    try:
        step_with_io.setup()

        # Mock Equiv_check to fail setup
        with patch("hagent.step.v2chisel_fix.v2chisel_fix.Equiv_check") as mock_eq, \
             patch("builtins.print") as mock_print:

            mock_eq_inst = MagicMock()
            mock_eq_inst.setup.return_value = False
            mock_eq_inst.get_error.return_value = "Yosys not found"
            mock_eq.return_value = mock_eq_inst

            res = step_with_io.run({
                "chisel_pass1": {
                    "chisel_changed": "class MyModule extends Module { val io = IO(new Bundle {}) }",
                    "verilog_candidate": "module mymodule(); endmodule",
                    "was_valid": True
                },
                "verilog_fixed": "module mymodule(); // fixed changes endmodule",
                "llm": {
                    "model": "test-model"
                }
            })

            # Verify error was printed
            mock_print.assert_any_call('[ERROR] Equiv_check setup failed: Yosys not found')

            # Verify 'chisel_fixed' reflects the setup failure
            cf = res["chisel_fixed"]
            assert cf["equiv_passed"] is False
            assert cf["refined_chisel"] == "class MyModule extends Module { val io = IO(new Bundle {}) }"
            assert cf.get("verilog_candidate") is None

    finally:
        # Cleanup: Remove 'prompt3.yaml' after the test
        if os.path.exists(prompt3_path):
            os.remove(prompt3_path)


def test_refine_chisel_code_empty_after_strip(step_with_io):
    """
    Test that an error is printed and original code is kept
    when LLM returns empty code after stripping backticks.
    """
    import hagent.step.v2chisel_fix.v2chisel_fix as fix_mod
    module_dir = os.path.dirname(os.path.abspath(fix_mod.__file__))
    prompt3_path = os.path.join(module_dir, "prompt3.yaml")

    # Create valid prompt3.yaml => top-level list
    with open(prompt3_path, "w") as f:
        f.write("""\
- role: system
  content: "Refinement system message"
""")

    try:
        step_with_io.setup()

        with patch.object(step_with_io.refine_llm, "chat", return_value="```chisel\n\n```"), \
             patch("builtins.print") as mock_print:

            original_code = "class MyModule extends Module { val io = IO(new Bundle {}) }"
            refined_code = step_with_io._refine_chisel_code(original_code, "Some LEC error")

            mock_print.assert_any_call('[ERROR] After removing backticks/fences, code is empty. Keeping old code.')
            assert refined_code == original_code
    finally:
        if os.path.exists(prompt3_path):
            os.remove(prompt3_path)


def test_generate_verilog_setup_failure(step_with_io):
    """
    Test that _generate_verilog returns (None, error_message) when Chisel2v.setup() fails.
    """
    step_with_io.setup()

    from hagent.tool.chisel2v import Chisel2v

    # Create a mock instance of Chisel2v with setup failing
    mock_c2v = MagicMock(spec=Chisel2v)
    mock_c2v.setup.return_value = False
    mock_c2v.error_message = 'Chisel2v setup failed due to missing dependencies.'

    with patch("hagent.step.v2chisel_fix.v2chisel_fix.Chisel2v", return_value=mock_c2v):
        verilog_output, error = step_with_io._generate_verilog("class MyModule extends Module {}", "shared_dir")

        # Verify the outputs
        assert verilog_output is None
        assert error == 'Chisel2v setup failed due to missing dependencies.'

def test_generate_verilog_missing_module_keyword(step_with_io):
    """
    Test that _generate_verilog returns an error when generated Verilog lacks 'module' keyword.
    """
    step_with_io.setup()

    # Mock Chisel2v.generate_verilog to return Verilog without 'module'
    with patch("hagent.step.v2chisel_fix.v2chisel_fix.Chisel2v.setup", return_value=True), \
         patch("hagent.step.v2chisel_fix.v2chisel_fix.Chisel2v.generate_verilog", return_value="// No mod keyword here"), \
         patch("builtins.print") as mock_print:

        verilog_output, error = step_with_io._generate_verilog("class MyModule extends Module {}", "shared_dir")

        # Verify that an error is returned
        assert verilog_output is None
        assert error == "Generated Verilog missing 'module' keyword."

def test_refinement_with_verilog_generation_failure(step_with_io, tmp_path):
    """
    Test the scenario where Verilog generation fails during the refinement loop,
    triggering the error message and continuation.
    """
    step_with_io.setup()
    step_with_io.lec_limit = 3  # Allows multiple iterations for testing

    # Mock LLM to return refined code that triggers a Verilog generation failure
    step_with_io.refine_llm = MagicMock()
    step_with_io.refine_llm.chat.return_value = "refined Chisel code"

    # Mock Equiv_check to initially fail and then not be called again due to generation failure
    mock_eq_inst = MagicMock()
    mock_eq_inst.setup.return_value = True
    mock_eq_inst.check_equivalence.return_value = (False, "LEC mismatch")  # Initial LEC failure

    # Mock _generate_verilog to fail during refinement attempts
    def mock_generate_verilog(chisel_code, shared_dir):
        if "refined" in chisel_code:
            return (None, 'Chisel2v failed')
        return ("module valid_verilog(); endmodule", None)

    with patch.object(step_with_io, "_generate_verilog", side_effect=mock_generate_verilog), \
         patch("builtins.print") as mock_print:

        # Setup input data for the run method
        input_data = {
            "chisel_pass1": {
                "chisel_changed": "initial Chisel code",
                "verilog_candidate": "initial Verilog",
                "was_valid": True
            },
            "verilog_fixed": "module fixed_verilog(); endmodule"
        }

        # Run the run method
        res = step_with_io.run(input_data)

        # Check that the appropriate error message was printed
        mock_print.assert_any_call("[ERROR] Verilog generation failed on iteration 1: Chisel2v failed")

        # Check final result
        cf = res["chisel_fixed"]
        assert cf["equiv_passed"] is False, "Expected equivalence check to fail due to Verilog generation failure"
        assert "refined Chisel code" in cf["refined_chisel"], "Refined Chisel code should be present despite failure"


def test_successful_verilog_generation_no_error(step_with_io):
    """
    Test _generate_verilog function to handle successful Verilog generation with no error message.
    """
    step_with_io.setup()

    # Simulate successful Verilog generation
    with patch.object(step_with_io, "_generate_verilog", return_value=("module successful_verilog(); endmodule", None)) as mock_gen:
        verilog_output, error = step_with_io._generate_verilog("class MyModule extends Module {}", "shared_dir")

        # Verify that the Verilog output is correct and error is None
        assert verilog_output == "module successful_verilog(); endmodule"
        assert error is None



def test_setup_prompt3_exists_but_empty_llm_config(tmp_path):
    """
    If prompt3.yaml exists and 'llm' config is empty => print warning and refine_llm=None
    """
    import sys
    from hagent.step.v2chisel_fix.v2chisel_fix import V2ChiselFix

    # Get the module's directory
    module = sys.modules[V2ChiselFix.__module__]
    class_dir = os.path.dirname(os.path.abspath(module.__file__))
    prompt3_path = os.path.join(class_dir, "prompt3.yaml")
    prompt3_path_contents = """\
messages:
  - role: system
    content: "This is prompt3 for refinement."
"""
    with open(prompt3_path, "w") as f:
        f.write(prompt3_path_contents)

    try:
        # Create an input file with 'llm' key but empty
        content = """\
chisel_pass1:
  chisel_changed: |
    class MyModule extends Module { val io = IO(new Bundle {}) }
  verilog_candidate: |
    module mymodule();
    endmodule
  was_valid: true

verilog_fixed: |
  module mymodule();
  endmodule

llm: {}
"""
        input_file = tmp_path / "input_empty_llm.yaml"
        input_file.write_text(content)

        step_obj = V2ChiselFix()
        out_file = tmp_path / "output_empty_llm.yaml"
        step_obj.set_io(inp_file=str(input_file), out_file=str(out_file))

        with patch("builtins.print") as mock_print:
            step_obj.setup()

            # Verify that the specific warning was printed
            mock_print.assert_any_call("[WARN] prompt3.yaml found but no 'llm' config. Can't refine automatically.")
            assert step_obj.refine_llm is None
    finally:
        if os.path.exists(prompt3_path):
            os.remove(prompt3_path)


def test_generate_verilog_success(step_with_io):
    """
    Test _generate_verilog successfully returns (verilog_output, None)
    """
    step_with_io.setup()
    
    with patch("hagent.step.v2chisel_fix.v2chisel_fix.Chisel2v.setup", return_value=True), \
         patch("hagent.step.v2chisel_fix.v2chisel_fix.Chisel2v.generate_verilog", return_value="module successful(); endmodule"):
        
        verilog_output, error = step_with_io._generate_verilog("class MyModule extends Module {}", "shared_dir")
        
        assert verilog_output == "module successful(); endmodule"
        assert error is None






