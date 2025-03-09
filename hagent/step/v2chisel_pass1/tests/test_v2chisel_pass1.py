import sys
import os
import tempfile
import yaml
import argparse
import pytest

# Import the module under test.
from hagent.step.v2chisel_pass1 import v2chisel_pass1

# --- Dummy implementations to override external dependencies ---

def dummy_extract_keywords_from_diff(diff):
    # Return dummy keyword(s) from the diff.
    return "dummy_keyword"

class DummyFuzzyGrep:
    def setup(self, mode):
        return True
    def search(self, text, search_terms, context, threshold):
        # Return a dummy search result with one matching line.
        return {"text": [(1, "dummy line from fuzzy", True)]}

def dummy_filter_lines(diff_file, chisel_file, context):
    # Return a dummy filtered hint line.
    return "->1: dummy line from filter_lines"

def dummy_inference(prompt_dict, prompt_index, n):
    # Return a dummy diff that the ChiselDiffApplier will use.
    return ["---dummy diff---"]

def dummy_generate_verilog(chisel_code, module_name):
    # Simulate generation of valid verilog.
    return "module dummy_module;"

def dummy_apply_diff(generated_diff, chisel_original):
    # Simulate a diff application that appends a comment.
    return chisel_original + "\n// diff applied"

def dummy_setup_chisel2v():
    return True

# Dummy classes to replace LLM_template and LLM_wrap.
class DummyTemplate:
    def __init__(self, config):
        self.template_dict = config
    def format(self, prompt_dict):
        # For testing, return a dummy prompt response.
        return [{"role": "user", "content": "---dummy diff---"}]

class DummyLLMWrap:
    def __init__(self, **kwargs):
        self.name = "v2chisel_pass1"
        self.last_error = ""
        self.chat_template = None
    def inference(self, prompt_dict, prompt_index, n):
        return dummy_inference(prompt_dict, prompt_index, n)

# --- Patch fixture to override dependencies in v2chisel_pass1 ---
@pytest.fixture(autouse=True)
def patch_dependencies(monkeypatch):
    # Patch FuzzyGrepFilter.extract_keywords_from_diff.
    monkeypatch.setattr(
        v2chisel_pass1.Extract_verilog_diff_keywords,
        "get_words",
        staticmethod(dummy_extract_keywords_from_diff)
    )
    # Patch Fuzzy_grep so that its setup returns True and search returns dummy result.
    from hagent.tool import fuzzy_grep
    monkeypatch.setattr(fuzzy_grep.Fuzzy_grep, "setup", lambda self, mode: True)
    monkeypatch.setattr(fuzzy_grep.Fuzzy_grep, "search", dummy_fuzzy_grep_search)

    # Patch FilterLines.filter_lines.
    from hagent.tool import filter_lines
    monkeypatch.setattr(filter_lines.FilterLines, "filter_lines", lambda self, diff_file, chisel_file, context: dummy_filter_lines(diff_file, chisel_file, context))

    # Patch LLM_wrap to use our DummyLLMWrap.
    monkeypatch.setattr(v2chisel_pass1, "LLM_wrap", lambda **kwargs: DummyLLMWrap(**kwargs))

    # Patch LLM_template to always load a dummy configuration.
    dummy_config = {
        'v2chisel_pass1': {
            'llm': {},
            'threshold': 40,
            'prompt1': "dummy prompt",
            'prompt2': "dummy prompt",
            'prompt3': "dummy prompt",
            'prompt4': "dummy prompt",
        }
    }
    monkeypatch.setattr(v2chisel_pass1, "LLM_template", lambda conf_file: DummyTemplate(dummy_config))

    # Patch Chisel2v: setup returns True and generate_verilog returns dummy verilog.
    from hagent.tool import chisel2v
    monkeypatch.setattr(chisel2v.Chisel2v, "setup", lambda self: dummy_setup_chisel2v())
    monkeypatch.setattr(chisel2v.Chisel2v, "generate_verilog", lambda self, code, module_name: dummy_generate_verilog(code, module_name))

    # Patch ChiselDiffApplier.apply_diff.
    from hagent.tool import chisel_diff_applier
    monkeypatch.setattr(chisel_diff_applier.ChiselDiffApplier, "apply_diff", lambda self, diff, original: dummy_apply_diff(diff, original))


# Helper for Fuzzy_grep.search (needed for monkey patch above)
def dummy_fuzzy_grep_search(self, text, search_terms, context, threshold):
    return {"text": [(1, "dummy line from fuzzy", True)]}


# --- The actual test ---
def test_v2chisel_pass1(monkeypatch, tmp_path):
    # Create a temporary input YAML file.
    input_data = {
        "llm": {},
        "verilog_original": "module foo;",
        "verilog_fixed": "module foo_fixed;",
        "chisel_original": "class TestModule extends Module {}",
        "threshold": 40,
        "context": 1
    }
    input_yaml = tmp_path / "simple_risc.yaml"
    output_yaml = tmp_path / "out_simple_risc.yaml"
    with open(input_yaml, "w") as f:
        yaml.dump(input_data, f)

    # Simulate command-line arguments: -o output file and the input file.
    test_args = ["test_v2chisel_pass1.py", "-o", str(output_yaml), str(input_yaml)]
    monkeypatch.setattr(sys, "argv", test_args)

    # Parse command-line arguments as the script would.
    args = v2chisel_pass1.parse_arguments()

    # Create and set up the step.
    step = v2chisel_pass1.V2Chisel_pass1()
    # Instead of manually setting input_file and input_data, use set_io() to properly initialize.
    step.set_io(inp_file=str(input_yaml), out_file=str(output_yaml))
    # Also set input_data (if needed for this test).
    step.input_data = input_data
    step.setup()

    # Run the step.
    result = step.run(input_data)

    # Wrap literals as done in the main function.
    result = v2chisel_pass1.wrap_literals(result)

    # Dump the result to the output file using ruamel.yaml.
    from ruamel.yaml import YAML
    ruamel_yaml = YAML()
    ruamel_yaml.default_flow_style = False
    ruamel_yaml.indent(mapping=2, sequence=4, offset=2)
    with open(str(output_yaml), "w") as out_file:
        ruamel_yaml.dump(result, out_file)

    # Load the output YAML using ruamel.yaml.
    # (No additional constructor is needed if we use ruamel.yaml to dump.)
    ruamel_yaml_load = YAML(typ='safe')
    with open(str(output_yaml)) as f:
        output = ruamel_yaml_load.load(f)

    assert "chisel_pass1" in output
    assert output["chisel_pass1"]["was_valid"] is True
    assert "verilog_diff" in output
    # Optionally, check that the applied diff appended our marker.
    assert "// diff applied" in output["chisel_pass1"]["chisel_updated"]


# Allow the test to be run directly.
if __name__ == "__main__":
    sys.exit(pytest.main([__file__]))
