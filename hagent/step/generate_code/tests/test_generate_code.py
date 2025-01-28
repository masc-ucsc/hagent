# hagent/step/generate_code/tests/test_generate_code.py

import os
import shutil
import pytest
from unittest.mock import patch, MagicMock
from hagent.step.generate_code.generate_code import Generate_code


@pytest.fixture
def clean_generated_dir(tmp_path):
    """
    Fixture to provide a temporary directory and ensure cleanup after tests.
    """
    yield tmp_path
    # Teardown is handled automatically by tmp_path


def test_generate_missing_llm(tmp_path):
    """
    Test that setup fails when 'llm' is missing in input YAML.
    """
    # Create a bad_input.yaml without 'llm'
    bad_input = {
        "description": "Some description",
        "interface": "interface details",
    }
    inp_file = tmp_path / "bad_input.yaml"
    with open(inp_file, 'w') as f:
        import yaml
        yaml.safe_dump(bad_input, f)
    
    out_file = tmp_path / "test_generate_code_output.yaml"
    
    gen_step = Generate_code()
    gen_step.set_io(inp_file=str(inp_file), out_file=str(out_file))
    
    # Mock yaml.dump to prevent actual file writing
    with patch("hagent.core.step.yaml.dump") as mock_yaml_dump:
        # Expect ValueError due to missing 'llm'
        with pytest.raises(ValueError, match="llm arguments not set in input file"):
            gen_step.setup()
            gen_step.step()
        
        # Verify yaml.dump was called with error information
        mock_yaml_dump.assert_called_once()

def test_generate_code(tmp_path):
    """
    Test generating code with a full input YAML.
    """
    # Create full_adder.yaml with all necessary fields including 'llm'
    full_adder_input = {
        "llm": {
            "model": "test-model",
            "other_config": "value"
        },
        "description": "Generate a full adder in Verilog",
        "interface": "input a, b; output sum, carry;",
        "bench_response": "some response",
        "bench_stage": "stage1",
        "name": "full_adder"
    }
    inp_file = tmp_path / "full_adder.yaml"
    with open(inp_file, 'w') as f:
        import yaml
        yaml.safe_dump(full_adder_input, f)

    out_file = tmp_path / "test_generate_code_output.yaml"

    gen_step = Generate_code()
    gen_step.set_io(inp_file=str(inp_file), out_file=str(out_file))

    # Mock LLM_template and LLM_wrap
    with patch("hagent.step.generate_code.generate_code.LLM_template") as mock_llm_template, \
         patch("hagent.step.generate_code.generate_code.LLM_wrap") as mock_llm_wrap, \
         patch("hagent.core.step.yaml.dump") as mock_yaml_dump:

        # Mock the template's format method
        mock_template_instance = MagicMock()
        mock_template_instance.format.return_value = "formatted prompt with potato"
        mock_llm_template.return_value = mock_template_instance

        # Mock LLM_wrap's methods
        mock_lw_instance = MagicMock()
        mock_llm_wrap.return_value = mock_lw_instance
        mock_lw_instance.inference.return_value = ["```verilog\nmodule full_adder(a, b, sum, carry);\nendmodule\n```"]

        # Run setup and step
        gen_step.setup()
        res = gen_step.step()

        # Assertions
        assert "generated_code" in res, "'generated_code' not found in result."
        assert "verilog_file" in res, "'verilog_file' not found in result."
        assert "bench_response" in res, "'bench_response' not found in result."
        assert "bench_stage" in res, "'bench_stage' not found in result."

        generated = res['generated_code']
        assert isinstance(generated, list), "'generated_code' should be a list."
        assert len(generated) == 1, "Expected one generated code snippet."
        snippet = generated[0].strip()
        
        # Optionally, assert on raw generated_code
        expected_raw_snippet = "```verilog\nmodule full_adder(a, b, sum, carry);\nendmodule\n```"
        assert snippet == expected_raw_snippet, "Raw 'generated_code' snippet does not match expected format."

        # Read the processed verilog file
        verilog_file = res['verilog_file']
        assert os.path.exists(verilog_file), f"Verilog file '{verilog_file}' was not created."
        with open(verilog_file, 'r') as f:
            file_contents = f.read().strip()
            assert file_contents.startswith("module full_adder"), "Verilog file does not start with the expected module definition."

        # Check that yaml.dump was called to write the output
        mock_yaml_dump.assert_called_once()


def test_generate_custom_module_name(tmp_path):
    """
    Test generating code with a custom module name.
    """
    # Create input2.yaml with 'name' set to 'my_custom_module'
    input2 = {
        "llm": {
            "model": "test-model",
            "other_config": "value"
        },
        "description": "Generate a custom module",
        "interface": "input x, y; output z;",
        "bench_response": "response",
        "bench_stage": "stage2",
        "name": "my_custom_module"
    }
    inp_file = tmp_path / "input2.yaml"
    with open(inp_file, 'w') as f:
        import yaml
        yaml.safe_dump(input2, f)

    out_file = tmp_path / "test_generate_code_output2.yaml"

    gen_step = Generate_code()
    gen_step.set_io(inp_file=str(inp_file), out_file=str(out_file))

    # Mock LLM_template and LLM_wrap
    with patch("hagent.step.generate_code.generate_code.LLM_template") as mock_llm_template, \
         patch("hagent.step.generate_code.generate_code.LLM_wrap") as mock_llm_wrap, \
         patch("hagent.core.step.yaml.dump") as mock_yaml_dump:

        # Mock the template's format method
        mock_template_instance = MagicMock()
        mock_template_instance.format.return_value = "formatted prompt with potato"
        mock_llm_template.return_value = mock_template_instance

        # Mock LLM_wrap's methods
        mock_lw_instance = MagicMock()
        mock_llm_wrap.return_value = mock_lw_instance
        mock_lw_instance.inference.return_value = ["```verilog\nmodule my_custom_module(x, y, z);\nendmodule\n```"]

        # Run setup and step
        gen_step.setup()
        res = gen_step.step()

        # Assertions
        assert "generated_code" in res, "'generated_code' not found in result."
        assert "verilog_file" in res, "'verilog_file' not found in result."
        assert "bench_response" in res, "'bench_response' not found in result."
        assert "bench_stage" in res, "'bench_stage' not found in result."

        generated = res['generated_code']
        assert isinstance(generated, list), "'generated_code' should be a list."
        assert len(generated) == 1, "Expected one generated code snippet."
        snippet = generated[0].strip()
        
        # Optionally, assert on raw generated_code
        expected_raw_snippet = "```verilog\nmodule my_custom_module(x, y, z);\nendmodule\n```"
        assert snippet == expected_raw_snippet, "Raw 'generated_code' snippet does not match expected format."

        # Read the processed verilog file
        verilog_file = res['verilog_file']
        assert os.path.exists(verilog_file), f"Verilog file '{verilog_file}' was not created."
        with open(verilog_file, 'r') as f:
            file_contents = f.read().strip()
            assert file_contents.startswith("module my_custom_module"), "Verilog file does not start with the expected module definition."

        # Check that yaml.dump was called to write the output
        mock_yaml_dump.assert_called_once()

def test_generate_empty_description(tmp_path):
    """
    Test generating code with an empty description.
    """
    # Create empty_desc.yaml with 'description' empty
    empty_desc_input = {
        "llm": {
            "model": "test-model",
            "other_config": "value"
        },
        "description": "",
        "interface": "input a; output b;",
        "bench_response": "response_empty",
        "bench_stage": "stage_empty",
        "name": "empty_desc_module"
    }
    inp_file = tmp_path / "empty_desc.yaml"
    with open(inp_file, 'w') as f:
        import yaml
        yaml.safe_dump(empty_desc_input, f)

    out_file = tmp_path / "test_generate_code_output3.yaml"

    gen_step = Generate_code()
    gen_step.set_io(inp_file=str(inp_file), out_file=str(out_file))

    # Mock LLM_template and LLM_wrap
    with patch("hagent.step.generate_code.generate_code.LLM_template") as mock_llm_template, \
         patch("hagent.step.generate_code.generate_code.LLM_wrap") as mock_llm_wrap, \
         patch("hagent.core.step.yaml.dump") as mock_yaml_dump:

        # Mock the template's format method
        mock_template_instance = MagicMock()
        mock_template_instance.format.return_value = "formatted prompt with potato"
        mock_llm_template.return_value = mock_template_instance

        # Mock LLM_wrap's methods
        mock_lw_instance = MagicMock()
        mock_llm_wrap.return_value = mock_lw_instance
        mock_lw_instance.inference.return_value = ["```verilog\nmodule empty_desc_module(a, b);\nendmodule\n```"]

        # Run setup and step
        gen_step.setup()
        res = gen_step.step()

        # Assertions
        assert "generated_code" in res, "'generated_code' not found in result."
        assert "verilog_file" in res, "'verilog_file' not found in result."
        assert "bench_response" in res, "'bench_response' not found in result."
        assert "bench_stage" in res, "'bench_stage' not found in result."

        generated = res['generated_code']
        assert isinstance(generated, list), "'generated_code' should be a list."
        assert len(generated) == 1, "Expected one generated code snippet."
        snippet = generated[0].strip()
        
        # Optionally, assert on raw generated_code
        expected_raw_snippet = "```verilog\nmodule empty_desc_module(a, b);\nendmodule\n```"
        assert snippet == expected_raw_snippet, "Raw 'generated_code' snippet does not match expected format."

        # Read the processed verilog file
        verilog_file = res['verilog_file']
        assert os.path.exists(verilog_file), f"Verilog file '{verilog_file}' was not created."
        with open(verilog_file, 'r') as f:
            file_contents = f.read().strip()
            assert file_contents.startswith("module empty_desc_module"), "Verilog file does not start with the expected module definition."

        # Check that yaml.dump was called to write the output
        mock_yaml_dump.assert_called_once()

def test_generate_empty_llm_response(tmp_path):
    """
    Test generating code when LLM returns an empty response.
    """
    # Create input YAML with 'llm' and other necessary fields
    empty_response_input = {
        "llm": {
            "model": "test-model",
            "other_config": "value"
        },
        "description": "Generate a module with empty LLM response",
        "interface": "input a; output b;",
        "bench_response": "response_empty",
        "bench_stage": "stage_empty",
        "name": "empty_response_module"
    }
    inp_file = tmp_path / "empty_response.yaml"
    with open(inp_file, 'w') as f:
        import yaml
        yaml.safe_dump(empty_response_input, f)

    out_file = tmp_path / "test_generate_code_output_empty_response.yaml"

    gen_step = Generate_code()
    gen_step.set_io(inp_file=str(inp_file), out_file=str(out_file))

    # Mock LLM_template and LLM_wrap, and patch the 'error' method on the instance
    with patch("hagent.step.generate_code.generate_code.LLM_template") as mock_llm_template, \
         patch("hagent.step.generate_code.generate_code.LLM_wrap") as mock_llm_wrap, \
         patch("hagent.core.step.yaml.dump") as mock_yaml_dump, \
         patch.object(gen_step, 'error') as mock_error:

        # Mock the template's format method
        mock_template_instance = MagicMock()
        mock_template_instance.format.return_value = "formatted prompt with potato"
        mock_llm_template.return_value = mock_template_instance

        # Mock LLM_wrap's methods to return an empty list
        mock_lw_instance = MagicMock()
        mock_llm_wrap.return_value = mock_lw_instance
        mock_lw_instance.inference.return_value = []

        # Run setup (should not raise)
        gen_step.setup()

        # Run step
        gen_step.step()

        # Ensure error was called with the correct message
        mock_error.assert_called_once_with("LLM returned an empty response.")

        # Ensure yaml.dump was called to write the error
        mock_yaml_dump.assert_called_once()



