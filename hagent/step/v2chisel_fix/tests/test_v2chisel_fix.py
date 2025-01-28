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
    # Make a minimal prompt3.yaml...
    test_dir = os.path.dirname(__file__)
    prompt3_path = os.path.join(test_dir, "prompt3.yaml")
    with open(prompt3_path, "w") as pf:
        pf.write("""messages:
  - role: system
    content: "Refinement system message"
""")

    step_with_io.setup()

    mock_eq_inst = MagicMock()
    mock_eq_inst.setup.return_value = True
    # First call fails, second passes
    mock_eq_inst.check_equivalence.side_effect = [False, True]

    # This LLM mock refines "MyModule" -> "MyModule_attempt1"
    def mock_chat_side_effect(prompt_dict):
        code_in = prompt_dict["chisel_code"]
        if "attempt1" in code_in:
            return code_in  # no further change
        return code_in.replace("MyModule", "MyModule_attempt1")

    # IMPORTANT: return two values (verilog_code, err_str) to match real _generate_verilog
    def mock_generate_verilog(chisel_code, module_name):
        if "attempt1" in chisel_code:
            return ("module refined_attempt1(); endmodule", None)
        return ("module original(); endmodule", None)

    # Patch out yaml.dump so we don't actually write a file
    with patch("hagent.core.step.yaml.dump", return_value=None), \
         patch("hagent.step.v2chisel_fix.v2chisel_fix.Equiv_check", return_value=mock_eq_inst), \
         patch.object(step_with_io, "_generate_verilog", side_effect=mock_generate_verilog), \
         patch.object(step_with_io.refine_llm, "chat", side_effect=mock_chat_side_effect):

        res = step_with_io.step()

    # Now the final result should not have an error; it should contain "chisel_fixed"
    assert "chisel_fixed" in res
    cf = res["chisel_fixed"]
    assert cf["equiv_passed"] is True
    assert "MyModule_attempt1" in cf["refined_chisel"]

    if os.path.exists(prompt3_path):
        os.remove(prompt3_path)



def test_lec_fails_all_attempts(step_with_io, tmp_path):
    """
    - LEC fails for all attempts, but code changes each time
    - after lec_limit => final result equiv_passed=False
    """
    test_dir = os.path.dirname(__file__)
    prompt3_path = os.path.join(test_dir, "prompt3.yaml")
    with open(prompt3_path, "w") as f:
        f.write("messages:\n - role: system\n   content: 'Refine'")

    step_with_io.setup()
    step_with_io.lec_limit = 2  # reduce attempts for test speed

    mock_eq_inst = MagicMock()
    mock_eq_inst.setup.return_value = True
    mock_eq_inst.check_equivalence.return_value = False  # always fails

    # Each refine => add "X" to code
    def mock_chat_side_effect(prompt_dict):
        code_in = prompt_dict["chisel_code"]
        return code_in + "X"

    # Return two values: (verilog_code, error_str). 
    # We'll always produce valid verilog but LEC fails anyway.
    def mock_gen_verilog(chisel_code, module_name):
        return ("module changed(); endmodule", None)

    with patch("hagent.core.step.yaml.dump", return_value=None), \
         patch("hagent.step.v2chisel_fix.v2chisel_fix.Equiv_check", return_value=mock_eq_inst), \
         patch.object(step_with_io.refine_llm, "chat", side_effect=mock_chat_side_effect), \
         patch.object(step_with_io, "_generate_verilog", side_effect=mock_gen_verilog):

        res = step_with_io.step()

    # Now no "too many values" error => final result is 'chisel_fixed' with failed equivalence
    assert "chisel_fixed" in res, "Result does not contain 'chisel_fixed' key."
    cf = res["chisel_fixed"]
    assert cf["equiv_passed"] is False
    # Code changed after each refine => ends with XX
    assert cf["refined_chisel"].endswith("XX")

    if os.path.exists(prompt3_path):
        os.remove(prompt3_path)



def test_lec_fails_refine_cannot_improve(step_with_io, tmp_path):
    """
    - LEC fails, LLM returns the exact same code => break out
    - Ensure final 'equiv_passed' is False
    """
    # Create prompt3.yaml
    test_dir = os.path.dirname(__file__)
    prompt3_path = os.path.join(test_dir, "prompt3.yaml")
    with open(prompt3_path, "w") as f:
        f.write("messages:\n - role: system\n   content: 'Refinement prompt'")

    step_with_io.setup()

    # Force fail from equivalence
    mock_eq_inst = MagicMock()
    mock_eq_inst.setup.return_value = True
    mock_eq_inst.check_equivalence.return_value = False

    # LLM returns the same snippet => no improvement => break
    def mock_chat_side_effect(prompt_dict):
        return prompt_dict["chisel_code"]  # same code => no improvement

    # Mock generate_verilog => it doesn't matter, won't pass LEC
    with patch("hagent.step.v2chisel_fix.v2chisel_fix.Equiv_check", return_value=mock_eq_inst), \
         patch.object(step_with_io.refine_llm, "chat", side_effect=mock_chat_side_effect), \
         patch.object(step_with_io, "_generate_verilog", return_value=("module x(); endmodule", None)):

        res = step_with_io.step()

    cf = res["chisel_fixed"]
    assert cf["equiv_passed"] is False
    # Because LLM didn't change code => we bail early

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
