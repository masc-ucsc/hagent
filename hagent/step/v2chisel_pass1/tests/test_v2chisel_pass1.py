import os
import pytest
from unittest.mock import patch

from hagent.step.v2chisel_pass1.v2chisel_pass1 import V2ChiselPass1


@pytest.fixture
def valid_input_file(tmp_path):
    """
    Create a valid input YAML file with 'llm' and minimal verilog/chisel data.
    """
    content = """\
llm:
  model: "test-model"
verilog_original: |
  module mymodule(input clk, rst);
  endmodule
verilog_fixed: |
  module mymodule(input clk, rst);
  // fixed changes
  endmodule
chisel_original: |
  class MyModule extends Module {
    val io = IO(new Bundle {})
  }
"""
    fpath = tmp_path / "input_valid.yaml"
    fpath.write_text(content)
    return str(fpath)



@pytest.fixture
def step_with_io(valid_input_file, tmp_path):
    """
    Return a V2ChiselPass1 Step object with a valid input path and a temp output path.
    NOTE: We won't call .setup() here; each test can do so at the desired time.
    """
    step_obj = V2ChiselPass1()
    out_file = str(tmp_path / "output.yaml")
    step_obj.set_io(inp_file=valid_input_file, out_file=out_file)
    return step_obj


def test_retry_and_prompt2_used(step_with_io, tmp_path):
    import os
    from unittest.mock import patch

    test_dir = os.path.dirname(__file__)
    prompt2_path = os.path.join(test_dir, "prompt2.yaml")

    with open(prompt2_path, "w") as f:
        f.write("messages:\n  - role: system\n    content: 'This is prompt2.yaml'")

    # We'll return invalid on attempt #1 (empty), valid on attempt #2
    mock_responses = [
        "",  # attempt #1 => empty => invalid
        """```chisel
class MyModule extends Module {
  val io = IO(new Bundle {})
}
```"""
    ]

    def mock_inference_side_effect(*args, **kwargs):
        if mock_responses:
            return [mock_responses.pop(0)]
        return ["No more responses"]

    # Because we're patching the *instance* method, only one arg is passed to our mock
    def mock_run_chisel2v(chisel_code):
        if not chisel_code.strip():
            return (False, None, "Chisel snippet is empty")
        return (True, "module MyModule(); endmodule", "")

    step_with_io.setup()

    # Patch the bound method on the step_with_io instance
    with patch.object(step_with_io, "_run_chisel2v", side_effect=mock_run_chisel2v):
        with patch.object(step_with_io.lw, "inference", side_effect=mock_inference_side_effect):
            res = step_with_io.step()

    if os.path.exists(prompt2_path):
        os.remove(prompt2_path)

    chisel_data = res["chisel_pass1"]
    assert chisel_data["was_valid"] is True, "Expected success after 2nd attempt"
    assert "module MyModule()" in chisel_data["verilog_candidate"]




def test_no_valid_snippet_generated(step_with_io):
    """
    - LLM never produces valid code after all attempts (empty or invalid).
    - We expect 'No valid snippet generated.' in chisel_changed and was_valid=False.
    """
    # Force all attempts to return invalid or empty
    mock_responses = [
        "",                # Attempt 1 => empty
        "garbage snippet", # Attempt 2 => no 'class ... extends Module'
        "still not valid", # Attempt 3
        "again invalid",   # Attempt 4
        ""                 # Attempt 5 => empty
    ]

    def mock_inference_side_effect(*args, **kwargs):
        if mock_responses:
            return [mock_responses.pop(0)]
        return ["No more responses"]

    step_with_io.setup()

    with patch.object(step_with_io.lw, "inference", side_effect=mock_inference_side_effect):
        res = step_with_io.step()

    chisel_data = res["chisel_pass1"]
    assert chisel_data["was_valid"] is False
    assert chisel_data["chisel_changed"] == "No valid snippet generated."


def test_chisel2v_empty_snippet(step_with_io):
    """
    - LLM returns a snippet that is empty after _strip_markdown_fences.
    - _run_chisel2v should detect empty snippet and fail immediately.
    """
    step_with_io.setup()

    with patch.object(step_with_io.lw, "inference", return_value=["```chisel\n\n```"]):
        res = step_with_io.step()

    chisel_data = res["chisel_pass1"]
    assert chisel_data["was_valid"] is False, "Expected was_valid=False with empty snippet"


def test_chisel2v_no_module_keyword(step_with_io):
    """
    Force all attempts to produce Verilog with *no* 'module' substring => remain invalid.
    Expect final was_valid=False and "No valid snippet generated."
    """
    step_with_io.setup()

    # Use the same snippet each time so all 5 attempts fail.
    mock_responses = ["class MyModule extends Module {}"] * 5

    def side_effect(*args, **kwargs):
        return [mock_responses.pop(0)]

    # Return a string that does NOT contain 'module' at all:
    fake_verilog_output = "// no 'mod' here"

    with patch.object(step_with_io.lw, "inference", side_effect=side_effect):
        with patch("hagent.step.v2chisel_pass1.v2chisel_pass1.Chisel2v.generate_verilog",
                   return_value=fake_verilog_output):
            res = step_with_io.step()

    chisel_data = res["chisel_pass1"]
    assert chisel_data["was_valid"] is False, "Should remain invalid if 'module' not found"
    assert chisel_data["chisel_changed"] == "No valid snippet generated."
    assert chisel_data["verilog_candidate"] is None




def test_chisel2v_exception(step_with_io):
    """
    Chisel2v.generate_verilog throws an exception every time => all 5 attempts fail.
    Final snippet => 'No valid snippet generated.'
    """
    step_with_io.setup()

    mock_responses = ["class MyModule extends Module {}"] * 5  # same snippet each attempt

    def side_effect(*args, **kwargs):
        return [mock_responses.pop(0)]

    with patch.object(step_with_io.lw, "inference", side_effect=side_effect):
        with patch(
            "hagent.step.v2chisel_pass1.v2chisel_pass1.Chisel2v.generate_verilog",
            side_effect=RuntimeError("some internal error")
        ):
            res = step_with_io.step()

    chisel_data = res["chisel_pass1"]
    assert chisel_data["was_valid"] is False
    assert chisel_data["chisel_changed"] == "No valid snippet generated."
    assert chisel_data["verilog_candidate"] is None


def test_chisel_classname_extraction(step_with_io):
    """
    - `_find_chisel_classname` finds the class name if present.
    - If not found, fallback to 'MyModule'.
    """
    step_with_io.setup()

    snippet = """```chisel
class TopModule extends Module {
  val io = IO(new Bundle {})
}
```"""

    with patch.object(step_with_io.lw, "inference", return_value=[snippet]):
        with patch("hagent.step.v2chisel_pass1.v2chisel_pass1.Chisel2v.generate_verilog",
                   return_value="module TopModule(); endmodule"):
            res = step_with_io.step()

    chisel_data = res["chisel_pass1"]
    assert chisel_data["was_valid"] is True
    assert "TopModule" in chisel_data["verilog_candidate"]

    # If the snippet has no class name => fallback
    snippet2 = "```chisel\n// no class definition\n```"
    with patch.object(step_with_io.lw, "inference", return_value=[snippet2]):
        with patch("hagent.step.v2chisel_pass1.v2chisel_pass1.Chisel2v.generate_verilog",
                   return_value="module MyModule(); endmodule"):
            res2 = step_with_io.step()

    chisel_data2 = res2["chisel_pass1"]
    assert chisel_data2["was_valid"] is True
    assert "MyModule" in chisel_data2["verilog_candidate"]
