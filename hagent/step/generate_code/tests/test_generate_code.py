# See LICENSE for details

import os
import shutil
import pytest

from hagent.step.generate_code.generate_code import Generate_code


def test_generate_missing_llm():
    test_dir = os.path.dirname(os.path.abspath(__file__))

    inp_file = os.path.join(test_dir, 'bad_input.yaml')

    trivial_step = Generate_code()
    trivial_step.set_io(inp_file=inp_file, out_file='test_generate_code_output.yaml')

    with pytest.raises(ValueError):
        trivial_step.setup()
        trivial_step.step()


@pytest.fixture
def clean_generated_dir():
    # Setup code (if any) goes here
    yield  # Test functions run after this line

    # Teardown code: remove any directories you know are created, e.g. 'default_module'
    if os.path.exists('default_module'):
        shutil.rmtree('default_module')
    if os.path.exists('my_custom_module'):
        shutil.rmtree('my_custom_module')
    if os.path.exists('empty_desc_module'):
        shutil.rmtree('empty_desc_module')


def test_generate_code():
    test_dir = os.path.dirname(os.path.abspath(__file__))

    inp_file = os.path.join(test_dir, 'full_adder.yaml')

    gen_step = Generate_code()
    gen_step.set_io(inp_file=inp_file, out_file='test_generate_code_output.yaml')

    gen_step.setup()
    res = gen_step.step()

    generated = res.get('generated_code')
    assert isinstance(generated, list)
    assert len(generated) == 1

    snippet = generated[0].strip()
    assert snippet, 'LLM returned an empty code snippet'
    # xx = res['generated_code']
    # print(f'generated_code:{xx}')

    verilog_file = res.get('verilog_file')
    assert verilog_file, "No 'verilog_file' key found in output"
    assert os.path.exists(verilog_file), f'Verilog file {verilog_file} was not created'

    with open(verilog_file, 'r', encoding='utf-8') as f:
        file_contents = f.read().strip()
        assert file_contents, f'The file {verilog_file} is empty'

    bench_response = res.get('bench_response')
    bench_stage = res.get('bench_stage')

    print(f'Generated code:\n{snippet}')
    print(f'Verilog file: {verilog_file}')
    print(f'bench_response: {bench_response}')
    print(f'bench_stage: {bench_stage}')


def test_generate_custom_module_name(clean_generated_dir):
    test_dir = os.path.dirname(os.path.abspath(__file__))

    # Suppose we have a YAML that sets 'name: my_custom_module'
    inp_file = os.path.join(test_dir, 'input2.yaml')  # create this to contain name: my_custom_module

    gen_step = Generate_code()
    gen_step.set_io(inp_file=inp_file, out_file='test_generate_code_output2.yaml')

    gen_step.setup()
    res = gen_step.step()

    # Check that 'my_custom_module' folder exists
    verilog_file = res.get('verilog_file')
    assert verilog_file, "No 'verilog_file' key found in output"

    # Should be something like "my_custom_module/my_custom_module.v"
    folder_name, filename = os.path.split(verilog_file)
    assert os.path.basename(folder_name) == 'my_custom_module'
    assert filename == 'my_custom_module.v'
    assert os.path.exists(verilog_file), f'{verilog_file} was not created'


def test_generate_empty_description(clean_generated_dir):
    test_dir = os.path.dirname(os.path.abspath(__file__))

    # Suppose 'empty_desc.yaml' includes an llm section, but no 'description' or it's empty
    inp_file = os.path.join(test_dir, 'empty_desc.yaml')

    gen_step = Generate_code()
    gen_step.set_io(inp_file=inp_file, out_file='test_generate_code_output3.yaml')

    gen_step.setup()
    res = gen_step.step()

    # As long as 'llm' exists, it may produce some fallback snippet
    generated = res.get('generated_code')
    assert isinstance(generated, list), "Expected 'generated_code' to be a list"
    assert len(generated) >= 1, 'LLM should produce at least one snippet even if description is empty'

    # Check the file
    verilog_file = res.get('verilog_file')
    assert verilog_file
    assert os.path.exists(verilog_file), f'{verilog_file} not found'


if __name__ == '__main__':  # pragma: no cover
    test_generate_missing_llm()
    test_generate_code()
    test_generate_empty_description()
    test_generate_custom_module_name()
