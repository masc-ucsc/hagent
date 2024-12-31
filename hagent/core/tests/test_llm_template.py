# See LICENSE for details

import os
import yaml
from hagent.core.llm_template import LLM_template


def test_llm_template_good():
    good_template = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'llm_template_good_inp.yaml')

    temp = LLM_template(good_template)
    d = temp.format({'xx': 'potato'})

    dir = os.path.dirname(os.path.abspath(__file__))
    out_file = os.path.join(dir, 'llm_template_good_out.yaml')
    with open(out_file, 'r') as f:
        good_out = yaml.safe_load(f)

    # print(f"d       :{d}")
    # print(f"good_out:{good_out}")
    assert d == good_out


# if __name__ == '__main__':  # pragma: no cover
#     test_llm_template_good()

def test_llm_template_file_not_found(): # test for when yaml file dne
    temp = LLM_template("nonexistent.yaml")
    assert "error" in temp.template_dict
    assert "does not exist" in temp.template_dict["error"]

def test_llm_template_empty_string():  # test with an empty string as input
    try:
        temp = LLM_template("invalid_file_name.yaml")  
    except Exception as e:
        assert isinstance(e, FileNotFoundError)


def test_llm_template_invalid_yaml(): # test when yaml contains invalid syntax
    invalid_yaml = os.path.join(
        os.path.dirname(os.path.abspath(__file__)), "invalid_yaml.yaml"
    )
    with open(invalid_yaml, "w") as f:
        f.write("invalid: [unclosed-bracket")
    temp = LLM_template(invalid_yaml)
    assert "error" in temp.template_dict
    assert "did not parse correctly" in temp.template_dict["error"]
    assert "invalid_yaml.yaml" in temp.template_dict["error"]


def test_validate_template_direct(): # directly testing 'validate_template' method
    temp = LLM_template({})  
    error_message = temp.validate_template([])
    assert error_message == "the list is empty."

    error_message = temp.validate_template([{"role": "invalid"}])
    assert error_message == "item at index 0 is missing the 'content' key."

    error_message = temp.validate_template([{"content": "hello"}])
    assert error_message == "item at index 0 is missing the 'role' key."

    error_message = temp.validate_template([{"role": "invalid", "content": "hello"}])
    assert (
        error_message
        == "invalid role 'invalid' at index 0. Allowed roles are 'user', 'system', or 'assistant'."
    )

    error_message = temp.validate_template(
        [{"role": "user", "content": "hello"}, {"role": "assistant", "content": "response"}]
    )
    assert error_message == "the last item's role must be 'user'."

    error_message = temp.validate_template(["string_item"])
    assert error_message == "item at index 0 is not a dictionary."

    error_message = temp.validate_template(
    [{"role": "user", "content": "hello"}, {"role": "user", "content": "response"}]
    )
    assert error_message is None 

def test_validate_template_unexpected_data():  # test validate_template with non-dict data
    temp = LLM_template({})
    error_message = temp.validate_template([12345])  
    assert error_message == "item at index 0 is not a dictionary."


def test_validate_template_missing_keys(): # test template that's missing required keys
    temp = LLM_template([{"role": "user"}])  
    assert "error" in temp.template_dict
    assert "item at index 0 is missing the 'content' key" in temp.template_dict["error"]

def test_validate_template_invalid_role(): # test template that contains invalid role
    temp = LLM_template([{"role": "invalid", "content": "hello"}])
    assert "error" in temp.template_dict
    assert "invalid role 'invalid' at index 0" in temp.template_dict["error"]


def test_validate_template_empty_list(): # test empty template list
    temp = LLM_template([])  
    assert "error" in temp.template_dict
    assert "the list is empty" in temp.template_dict["error"]

def test_llm_template_unsupported_input(): # test when input is unsupported type
    temp = LLM_template(12345)  
    assert "error" in temp.template_dict
    assert "could not process {str}" in temp.template_dict["error"]
    

# def test_llm_template_unsupported_data_type():  # test with unsupported types like float and bool
    temp = LLM_template(12.34)  
    assert "error" in temp.template_dict
    assert "could not process {str}" in temp.template_dict["error"]

    temp = LLM_template(True)  
    assert "error" in temp.template_dict
    assert "could not process {str}" in temp.template_dict["error"]
    


def test_llm_template_format_undefined_variable(): # test when context is missing varibales required by templates
    good_template = os.path.join(
        os.path.dirname(os.path.abspath(__file__)), "llm_template_good_inp.yaml"
    )
    temp = LLM_template(good_template)
    result = temp.format({"missing_key": "value"})
    assert "error" in result[0]
    assert "undefined variable" in result[0]["error"]


def test_llm_template_format_on_invalid_template(): # test when trying to format invalid template
    temp = LLM_template([{"role": "user"}])  
    result = temp.template_dict
    assert "error" in result
    assert "item at index 0 is missing the 'content' key" in result["error"]
    
    temp = LLM_template("nonexistent.yaml") 
    result = temp.format({"key": "value"})
    assert "error" in result
    assert "does not exist" in result["error"]

def test_llm_template_invalid_placeholder():  # test for invalid placeholders in the template
    good_template = os.path.join(
        os.path.dirname(os.path.abspath(__file__)), "llm_template_good_inp.yaml"
    )
    temp = LLM_template(good_template)
    # Missing key in the context
    result = temp.format({"unknown_key": "value"})
    assert "error" in result[0]
    assert "undefined variable" in result[0]["error"]


def test_llm_template_file_path_resolution():
    valid_yaml = os.path.join(
        os.path.dirname(os.path.abspath(__file__)), "valid_relative.yaml"
    )
    try:
        with open(valid_yaml, "w") as f:
            f.write("- role: user\n  content: Hello World")

        abs_path_template = LLM_template(valid_yaml)
        assert "error" not in abs_path_template.template_dict
        # assert abs_path_template.file_name == valid_yaml

        current_dir = os.getcwd()
        os.chdir(os.path.dirname(os.path.abspath(__file__)))
        try:
            relative_path = os.path.basename(valid_yaml)
            rel_path_template = LLM_template(relative_path)
            assert "error" not in rel_path_template.template_dict
        finally:
            os.chdir(current_dir)

    finally:
        if os.path.exists(valid_yaml):
            os.remove(valid_yaml)

if __name__ == "__main__":  # pragma: no cover
    test_llm_template_good()
    test_llm_template_file_not_found()
    test_llm_template_invalid_yaml()
    test_validate_template_missing_keys()
    test_validate_template_invalid_role()
    test_validate_template_empty_list()
    test_llm_template_unsupported_input()
    test_llm_template_format_undefined_variable()
    test_llm_template_format_on_invalid_template()
    test_llm_template_invalid_placeholder()
    test_llm_template_file_path_resolution()
    test_llm_template_empty_string()
    test_validate_template_unexpected_data()
