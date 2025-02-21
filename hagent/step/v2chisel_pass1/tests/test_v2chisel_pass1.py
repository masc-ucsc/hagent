import os
import pytest
from unittest.mock import patch

from hagent.step.v2chisel_pass1.v2chisel_pass1 import V2Chisel_pass1



def test_retry_and_prompt2_used(step_with_io, tmp_path):
    import os
    from unittest.mock import patch

    test_dir = os.path.dirname(__file__)
    prompt2_path = os.path.join(test_dir, 'prompt2.yaml')

    with open(prompt2_path, 'w') as f:
        f.write("messages:\n  - role: system\n    content: 'This is prompt2.yaml'")

    # We'll return invalid on attempt #1 (empty), valid on attempt #2
    mock_responses = [
        '',  # attempt #1 => empty => invalid
        """```chisel
class MyModule extends Module {
  val io = IO(new Bundle {})
}
```""",
    ]

    def mock_inference_side_effect(*args, **kwargs):
        if mock_responses:
            return [mock_responses.pop(0)]
        return ['No more responses']

    # Because we're patching the *instance* method, only one arg is passed to our mock
    def mock_run_chisel2v(chisel_code):
        if not chisel_code.strip():
            return (False, None, 'Chisel snippet is empty')
        return (True, 'module MyModule(); endmodule', '')

    step_with_io.setup()

    # Patch the bound method on the step_with_io instance
    with patch.object(step_with_io, '_run_chisel2v', side_effect=mock_run_chisel2v):
        with patch.object(step_with_io.lw, 'inference', side_effect=mock_inference_side_effect):
            res = step_with_io.step()

    if os.path.exists(prompt2_path):
        os.remove(prompt2_path)

    chisel_data = res['chisel_pass1']
    assert chisel_data['was_valid'] is True, 'Expected success after 2nd attempt'
    assert 'module MyModule()' in chisel_data['verilog_candidate']


def test_no_valid_snippet_generated(step_with_io):
    """
    - LLM never produces valid code after all attempts (empty or invalid).
    - We expect 'No valid snippet generated.' in chisel_updated and was_valid=False.
    """
    # Force all attempts to return invalid or empty
    mock_responses = [
        '',  # Attempt 1 => empty
        'garbage snippet',  # Attempt 2 => no 'class ... extends Module'
        'still not valid',  # Attempt 3
        'again invalid',  # Attempt 4
        '',  # Attempt 5 => empty
    ]

    def mock_inference_side_effect(*args, **kwargs):
        if mock_responses:
            return [mock_responses.pop(0)]
        return ['No more responses']

    step_with_io.setup()

    with patch.object(step_with_io.lw, 'inference', side_effect=mock_inference_side_effect):
        res = step_with_io.step()

    chisel_data = res['chisel_pass1']
    assert chisel_data['was_valid'] is False
    assert chisel_data['chisel_updated'] == 'No valid snippet generated.'


def test_chisel2v_empty_snippet(step_with_io):
    """
    - LLM returns a snippet that is empty after _strip_markdown_fences.
    - _run_chisel2v should detect empty snippet and fail immediately.
    """
    step_with_io.setup()

    with patch.object(step_with_io.lw, 'inference', return_value=['```chisel\n\n```']):
        res = step_with_io.step()

    chisel_data = res['chisel_pass1']
    assert chisel_data['was_valid'] is False, 'Expected was_valid=False with empty snippet'


def test_chisel2v_no_module_keyword(step_with_io):
    """
    Force all attempts to produce Verilog with *no* 'module' substring => remain invalid.
    Expect final was_valid=False and "No valid snippet generated.".
    """
    step_with_io.setup()

    # Use the same snippet each time so all 5 attempts fail.
    mock_responses = ['class MyModule extends Module {}'] * 5

    def side_effect(*args, **kwargs):
        return [mock_responses.pop(0)]

    # Return a string that does NOT contain 'module' at all:
    fake_verilog_output = "// no 'mod' here"

    with patch.object(step_with_io.lw, 'inference', side_effect=side_effect):
        with patch('hagent.step.v2chisel_pass1.v2chisel_pass1.Chisel2v.generate_verilog', return_value=fake_verilog_output):
            res = step_with_io.step()

    chisel_data = res['chisel_pass1']
    assert chisel_data['was_valid'] is False, "Should remain invalid if 'module' not found"
    assert chisel_data['chisel_updated'] == 'No valid snippet generated.'
    assert chisel_data['verilog_candidate'] is None


def test_chisel2v_exception(step_with_io):
    """
    Chisel2v.generate_verilog throws an exception every time => all 5 attempts fail.
    Final snippet => 'No valid snippet generated.'.
    """
    step_with_io.setup()

    mock_responses = ['class MyModule extends Module {}'] * 5  # same snippet each attempt

    def side_effect(*args, **kwargs):
        return [mock_responses.pop(0)]

    with patch.object(step_with_io.lw, 'inference', side_effect=side_effect):
        with patch(
            'hagent.step.v2chisel_pass1.v2chisel_pass1.Chisel2v.generate_verilog',
            side_effect=RuntimeError('some internal error')
        ):
            res = step_with_io.step()

    chisel_data = res['chisel_pass1']
    assert chisel_data['was_valid'] is False
    assert chisel_data['chisel_updated'] == 'No valid snippet generated.'
    assert chisel_data['verilog_candidate'] is None


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

    with patch.object(step_with_io.lw, 'inference', return_value=[snippet]):
        with patch(
            'hagent.step.v2chisel_pass1.v2chisel_pass1.Chisel2v.generate_verilog',
            return_value='module TopModule(); endmodule'
        ):
            res = step_with_io.step()

    chisel_data = res['chisel_pass1']
    assert chisel_data['was_valid'] is True
    assert 'TopModule' in chisel_data['verilog_candidate']

    # If the snippet has no class name => fallback
    snippet2 = '```chisel\n// no class definition\n```'
    with patch.object(step_with_io.lw, 'inference', return_value=[snippet2]):
        with patch(
            'hagent.step.v2chisel_pass1.v2chisel_pass1.Chisel2v.generate_verilog',
            return_value='module MyModule(); endmodule'
        ):
            res2 = step_with_io.step()

    chisel_data2 = res2['chisel_pass1']
    assert chisel_data2['was_valid'] is True
    assert 'MyModule' in chisel_data2['verilog_candidate']


def test_missing_llm_section(tmp_path):
    """
    Test that an error is raised when 'llm' section is missing in input YAML.
    """
    # Create input YAML without 'llm'
    missing_llm_input = {
        'verilog_original': 'module mymodule(input clk, rst); endmodule',
        'verilog_fixed': 'module mymodule(input clk, rst); // fixed changes endmodule',
        'chisel_original': 'class MyModule extends Module { val io = IO(new Bundle {}) }',
    }
    inp_file = tmp_path / 'input_missing_llm.yaml'
    with open(inp_file, 'w') as f:
        import yaml
        yaml.safe_dump(missing_llm_input, f)

    out_file = tmp_path / 'output_missing_llm.yaml'

    gen_step = V2Chisel_pass1()
    gen_step.set_io(inp_file=str(inp_file), out_file=str(out_file))

    # Patch the 'error' method to raise ValueError
    with patch.object(V2Chisel_pass1, 'error', side_effect=ValueError("Missing 'llm' section in input YAML")):
        with pytest.raises(ValueError, match="Missing 'llm' section in input YAML"):
            gen_step.setup()


def test_missing_prompt1_file(step_with_io, tmp_path):
    """
    Test that an error is raised when 'prompt1.yaml' file is missing.
    """
    import hagent.step.v2chisel_pass1.v2chisel_pass1

    prompt1_path = os.path.join(
        os.path.dirname(os.path.abspath(hagent.step.v2chisel_pass1.v2chisel_pass1.__file__)), 'prompt1.yaml'
    )

    # Patch 'os.path.exists' to return False for 'prompt1.yaml'
    with patch('hagent.step.v2chisel_pass1.v2chisel_pass1.os.path.exists', return_value=False), \
         patch('hagent.core.step.Step.error', side_effect=ValueError(f'Prompt file not found: {prompt1_path}')):
        with pytest.raises(ValueError, match=f'Prompt file not found: {prompt1_path}'):
            step_with_io.setup()


def test_llm_returns_empty_response(step_with_io):
    """
    Test handling when LLM returns an empty response.
    """
    step_with_io.setup()

    # Mock LLM_wrap.inference to return an empty list
    with patch.object(step_with_io.lw, 'inference', return_value=[]), patch('builtins.print') as mock_print:
        res = step_with_io.run(
            {
                'verilog_original': 'module mymodule(input clk, rst); endmodule',
                'verilog_fixed': 'module mymodule(input clk, rst); // fixed changes endmodule',
                'chisel_original': 'class MyModule extends Module { val io = IO(new Bundle {}) }',
                'llm': {'model': 'test-model', 'other_config': 'value'},
            }
        )

    # Check that the print statement was called
    mock_print.assert_any_call('\n=== LLM RESPONSE: EMPTY ===\n')

    # Verify that 'chisel_pass1' reflects the continued state
    chisel_data = res['chisel_pass1']
    assert chisel_data['was_valid'] is False
    assert chisel_data['chisel_updated'] == 'No valid snippet generated.'


def test_chisel2v_setup_failure(step_with_io):
    """
    Test that an error is returned when Chisel2v.setup() fails.
    """
    from hagent.tool.chisel2v import Chisel2v
    from unittest.mock import MagicMock

    step_with_io.setup()

    # Create a mock instance of Chisel2v
    mock_c2v = MagicMock(spec=Chisel2v)
    mock_c2v.setup.return_value = False
    mock_c2v.error_message = 'Initialization failed'

    # Patch the Chisel2v constructor to return the mock instance
    with patch('hagent.step.v2chisel_pass1.v2chisel_pass1.Chisel2v', return_value=mock_c2v):
        # Mock the inference method to return a valid Chisel snippet
        with patch.object(step_with_io.lw, 'inference', return_value=['```chisel\nclass MyModule extends Module {}\n```']):
            res = step_with_io.step()

    # Verify that 'chisel_pass1' reflects the setup failure
    chisel_data = res['chisel_pass1']
    assert chisel_data['was_valid'] is False
    assert chisel_data['chisel_updated'] == 'No valid snippet generated.'
    assert chisel_data['verilog_candidate'] is None
