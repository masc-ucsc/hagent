#!/usr/bin/env python3
import os
import sys
import tempfile
import pytest
from ruamel.yaml import YAML
from ruamel.yaml.scalarstring import LiteralScalarString
from unittest.mock import patch, MagicMock

# Import the module under test.
from hagent.step.v2chisel_pass1 import v2chisel_pass1

# --- Dummy implementations to override external dependencies ---

def dummy_extract_keywords_from_diff(diff):
    # Return a dummy keyword string.
    return "dummy_keyword"

# IMPORTANT: Return a numeric line (0) instead of 1 so that Code_scope works.
def dummy_fuzzy_grep_search(self, text, search_terms, threshold):
    return {"text": [(0, "dummy line from fuzzy", True)]}

def dummy_inference(prompt_dict, prompt_index, n):
    # Return a dummy diff string (with triple backticks that will be stripped).
    return ["```chisel\n---dummy diff---\n```"]

def dummy_setup_chisel2v():
    return True

def dummy_generate_verilog(chisel_code, module_name):
    # Return dummy verilog that includes the keyword "module"
    return "module dummy_module; endmodule"

def dummy_apply_diff(self, generated_diff, original):
    # Simulate applying a diff by appending a marker.
    return original + "\n// diff applied"

# Dummy classes to replace LLM_wrap and LLM_template.
class DummyTemplate:
    def __init__(self, config):
        self.template_dict = config
    def format(self, prompt_dict):
        # Return a dummy prompt (not used for further processing).
        return [{"role": "user", "content": "---dummy diff---"}]

class DummyLLMWrap:
    def __init__(self, **kwargs):
        self.name = kwargs.get("name", "v2chisel_pass1")
        self.last_error = ""
        self.chat_template = None
    def inference(self, prompt_dict, prompt_index, n):
        return dummy_inference(prompt_dict, prompt_index, n)

# --- Fixture to patch dependencies ---
@pytest.fixture(autouse=True)
def patch_dependencies(monkeypatch):
    # Patch the extraction of keywords.
    monkeypatch.setattr(v2chisel_pass1.Extract_verilog_diff_keywords,
                        "get_user_variables",
                        staticmethod(dummy_extract_keywords_from_diff))
    # Patch Fuzzy_grep: setup returns True and search returns our dummy result.
    from hagent.tool import fuzzy_grep
    monkeypatch.setattr(fuzzy_grep.Fuzzy_grep, "setup", lambda self, mode: True)
    monkeypatch.setattr(fuzzy_grep.Fuzzy_grep, "search", dummy_fuzzy_grep_search)
    # Patch LLM_wrap and LLM_template in our module.
    monkeypatch.setattr(v2chisel_pass1, "LLM_wrap", lambda **kwargs: DummyLLMWrap(**kwargs))
    dummy_config = {
        'v2chisel_pass1': {
            'llm': {},
            'threshold': 40,
            'prompt0': "dummy prompt",
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
    # Patch ChiselDiffApplier: apply_diff returns original code with marker appended.
    from hagent.tool import chisel_diff_applier
    monkeypatch.setattr(chisel_diff_applier.ChiselDiffApplier, "apply_diff", dummy_apply_diff)

# --- Fixture for valid input data ---
@pytest.fixture
def valid_input_data():
    return {
        "llm": {},
        "verilog_original": "module foo; endmodule",
        "verilog_fixed": "module foo_fixed; endmodule",
        "chisel_original": "class TestModule extends Module {}",
        "threshold": 40,
        "context": 1,
        "chisel_pass1": {
            "chisel_changed": "class TestModule extends Module {}",
            "verilog_candidate": "module foo(); endmodule",
            "was_valid": True,
            "chisel_subset": "class TestModule extends Module {}"
        }
    }

# --- Test for union_hints function ---
def test_union_hints():
    hints1 = "   1: first line\n-> 2: second line"
    hints2 = "-> 2: override second line\n   3: third line"
    union = v2chisel_pass1.union_hints(hints1, hints2)
    assert "->" in union
    assert "1:" in union
    assert "2:" in union
    assert "3:" in union
    assert "override second line" in union

# --- Main test for V2Chisel_pass1.run ---
def test_v2chisel_pass1_run(valid_input_data, tmp_path):
    yaml_obj = YAML()
    input_file = tmp_path / "input.yaml"
    output_file = tmp_path / "output.yaml"
    with open(input_file, "w") as f:
        yaml_obj.dump(valid_input_data, f)

    step = v2chisel_pass1.V2Chisel_pass1()
    step.set_io(inp_file=str(input_file), out_file=str(output_file))
    step.input_data = valid_input_data
    step.setup()
    
    # Call step.step() with no extra argument.
    result = step.step()
    result = v2chisel_pass1.wrap_literals(result)
    
    with open(str(output_file), "w") as out_f:
        yaml_obj.dump(result, out_f)
    
    with open(str(output_file)) as f:
        out_data = yaml_obj.load(f)
    
    assert "chisel_pass1" in out_data
    cp = out_data["chisel_pass1"]
    # Our dummy_inference returns a diff that will be stripped to '---dummy diff---'
    # and dummy_apply_diff appends "\n// diff applied" to chisel_original.
    assert cp["was_valid"] is True
    assert "TestModule" in cp["chisel_subset"]
    # We expect chisel_updated to equal "class TestModule extends Module {}" + "\n// diff applied"
    assert cp["chisel_updated"].endswith("// diff applied")
    assert "verilog_diff" in out_data

if __name__ == "__main__":
    sys.exit(pytest.main([__file__]))
