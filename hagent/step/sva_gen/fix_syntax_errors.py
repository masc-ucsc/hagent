# file.vc syntax are adjusted to slang compiler so that we could call test_react_compile_slang_simple.py in hagent to
# fix the syntax errors automatically， also need to set environment variables like $ROOT, $DUT_ROOT to run the hagent script

# To do:
# 1. in cache_ctrl.sv, src file path has one more level $ROOT/src/cache_subsystem/cache_ctrl.sv
# 2. in bind module, do not connect the instances like state_d/state_q
# 3. in bind module, remove replicated connections.
# 4. in bind module, do not connect signal declared automatic inside always_comb block
# 5. in property module, need to declare state machine states like state_d, state_q
# 6. in the prompt, need to modify that do not add comment between assertion lines
# 7. for assumption, need to unify the usage of rst_ni, use !rst_ni, not ~rst_ni or rst_ni

import re
import os
import argparse

import subprocess
#from cva6_main_formal import sva
from parse_jg_sva_log import jg_post_process
import yaml

from hagent.core.llm_wrap import LLM_wrap

#llm = LLM_wrap(name="default", conf_file=args.llm_conf, log_file=io_config["llm_log_file"])

# replace ' assert (' with ' assert property (' in the assertion file and replace 'MODULE' with the module name for initial debugging
def replace_assertions(file_path, module_name):
    with open(file_path, 'r') as file:
        lines = file.readlines()

    with open(file_path, 'w') as file:
        for line in lines:
            line = line.replace('assert (', 'assert property (')
            line = line.replace('MODULE', module_name)
            file.write(line)

# extract errors from the log file, and assertions from the assertion file
def extract_errors(log_file_path, compiler_flag):
    Jasper_error_pattern = r"^\[ERROR.*?\]\s.*?\((\d+)\):\s(.+)$"
    #Slang_error_pattern = '^(.+\.sv):(\d+):(\d+): error: (.+)$'
    Slang_error_pattern = r'^(.+\.sv):(\d+):(\d+): error: (.+)$'
    #always_comb_regex = r'always_comb\s+begin(?:\s+:\s*\w+)?\s*((?:[^e]|e(?!nd\b))*?)\s*end\b'

    errors = []

    if compiler_flag == 0:
        # extract Jasper log errors
        with open(log_file_path, 'r') as file:
            for line in file:
                match = re.match(Jasper_error_pattern, line)
                if match:
                    line_number = match.group(1)
                    error_message = match.group(2)
                    errors.append((line_number, error_message))
    else:
        # extract Slang output errors
        print('---------extracting error messages from slang output--------------')
        with open(log_file_path, 'r') as file:
            for line in file:
                match = re.match(Slang_error_pattern, line)
                if match:
                    line_number = match.group(2)
                    #error_message = match.group(2)
                    errors.append((line_number, line))
        print(errors)

    return errors

# get the assertion from the assertion file with the given line number
def extract_connected_assertions(file_path, line_number):

    file = open(file_path, 'r')
    lines = file.readlines()
    # Split the text into lines
    #lines = text.splitlines()

    # Check if the given line number is within the bounds
    #if line_number < 0 or line_number >= len(lines):
    #    raise ValueError("Line number is out of range.")

    # Find connected lines before the given line number
    start = line_number
    while start > 0 and lines[start - 1].strip():
        start -= 1

    # Find connected lines after the given line number
    end = line_number
    while end < len(lines) - 1 and lines[end + 1].strip():
        end += 1

    # Return the connected lines around the given line number
    return str(lines[start:end + 1])



def extract_property_blocks(file_path):
    result = []
    collect_lines = False
    current_block = []

    with open(file_path, 'r') as file:
        for line in file:
            stripped_line = line.strip()

            # Start collecting lines when encountering '// assertions/property below'
            if stripped_line.startswith('// assertions/property below'):
                collect_lines = True
                current_block = [line.strip()]  # Start a new block
                continue

            # Stop collecting when '// assertions/property above' is encountered
            if stripped_line.startswith('// assertions/property above') and collect_lines:
                current_block.append(line.strip())  # Add the last line to the block
                result.append("\n".join(current_block))  # Save the block
                collect_lines = False
                continue

            # Collect lines if we are inside the block
            if collect_lines:
                current_block.append(line.strip())

    return result

# write the fixed assertions without plain text explanation back to the assertion file
def write_back_fixed_sva(assertion_fix_temp_file, fixed_assertion_file):
    blocks = extract_property_blocks(assertion_fix_temp_file)
    sva_block = []
    for line in blocks:
        if '// assertions/property above' in line:
            line = line.replace('// assertions/property above', '')
        if '// assertions/property below' in line:
            line = line.replace('// assertions/property below', '')
        sva_block.append(line)

    #print(sva_block)
    with open(fixed_assertion_file, "a") as file:
        file.writelines(sva_block)

# delete the error assertions from the assertion file given the line number
def delete_error_sva(file_path, line_number):
    """
    Deletes lines surrounding a specified line number in a file until encountering
    an empty line above and below that line.

    Parameters:
    - file_path (str): Path to the file.
    - line_number (int): The line number around which lines will be deleted (1-based index).
    """
    # Read all lines from the file
    with open(file_path, 'r') as file:
        lines = file.readlines()

    # Adjust for 0-based index
    line_number -= 1

    # Find the start index (empty line above the line_number)
    start_index = line_number
    while start_index > 0:
        if start_index < len(lines) and lines[start_index - 1].strip() == "":
            break
        start_index -= 1

    # Find the end index (empty line below the line_number)
    end_index = line_number
    while end_index < len(lines) - 1:
        if lines[end_index + 1].strip() == "":
            break
        end_index += 1

    # Delete lines from start_index to end_index (inclusive)
    del lines[start_index:end_index + 1]

    # Write the modified lines back to the file
    with open(file_path, 'w') as file:
        file.writelines(lines)

    print("Error assertions deleted successfully.")

# send request to OpenAI API to fix the syntax error, and delete the sva from the sva object
#modified version
#def request_fix(error_message, sva_object, prop_index):
def request_fix(error_message, sva_object, prop_index, llm):

    if not error_message:
        print('---------Error message is empty-----------\n')
        return

    with open(sva_object.prop_location[prop_index], 'r') as file:
        prop_content = file.read()

    messages = [
        {"role": "system", "content": "You are an expert in fixing SystemVerilog code."},
        {"role": "user", "content": f"""The following is a property file for formal verification:

'{prop_content}'

It has the following error message from JasperGold with the line number and the error:
'{error_message}'.

Can you fix it? Only return the module that contains the fixed assertion, do not return plain text.
Do not use backticks to wrap the code. Do not modify the module port declaration. Do not modify the packages."""}
    ]

    prompt_dict = {
        "system": messages[0]["content"],
        "user": messages[1]["content"]
    }
    print('Sending to LLM...')
    print(prompt_dict)

    write_prompt_log(messages)
    response = llm.inference(prompt_dict, prompt_index="fix")

    if not response:
        print("No response received from LLM.")
        return

    fixed_code = response[0]
    print(fixed_code)
    write_prompt_log(fixed_code)

    with open(sva_object.prop_location[prop_index], 'w') as file:
        file.write(fixed_code)


# for each block's assertions, keep record of every prompt and response
def write_prompt_log(message):
    log_file_path = 'fix_prompt_log.txt'
    with open(log_file_path, 'a') as file:
        file.write(str(message))
        file.close()

# need to make sure Slang has needed packages in case of errors like below
# slang: /mada/software/cadence/JASPER24/Linux64/lib/libstdc++.so.6: version GLIBCXX_3.4.32' not found (required by slang)
# slang: /mada/software/cadence/JASPER24/Linux64/lib/libstdc++.so.6: version CXXABI_1.3.15' not found (required by slang)
# for the above mistake, run 'export LD_LIBRARY_PATH=/usr/lib64:$LD_LIBRARY_PATH'
def check_syntax_error_with_slang(sva_object):
    print('-------------------Checking syntax error with Slang---------------------\n')
    os.environ["LD_LIBRARY_PATH"] = "/usr/lib64:" + os.environ.get("LD_LIBRARY_PATH", "")
    slang_err_msg_file = 'syntax_error_slang.txt'
    if not os.path.exists(slang_err_msg_file):
        slang_err_msg_file = os.path.join(os.getcwd(), slang_err_msg_file)
    with open(slang_err_msg_file, 'w') as f:
        slang_proc = subprocess.Popen(f'slang ariane/src/include/riscv.sv ariane/include/ariane_pkg.sv ' + sva_object.prop_location + ' > syntax_error_slang.txt', stdout=subprocess.PIPE, stderr=subprocess.PIPE, preexec_fn=os.setsid, shell=True, text=True )
        #print('Slang stdout and stderr below\n')
        stdout, stderr = slang_proc.communicate()
        print(stdout)
        print(stderr)
        for line in stderr.splitlines():
            if ('error: unknown class or package' not in line):
                f.write(line + '\n')
    if stderr and 'error' in stderr:
        if 'error: unknown class or package' not in stderr:
            print('Found errors with Slang\n')
            return slang_err_msg_file
    else:
        print('Errors not found with Slang\n')
        return None

def delete_syntax_errors(error_output, sva_object):
    with open(sva_object.prop_location, 'r') as f:
        lines = f.readlines()
    # extract jasper log errors
    error_tuples = extract_errors(error_output, 0)
    # if slang outputs error messages
    if error_tuples:
        error_lines = [t[0] for t in error_tuples]
        lines_to_remove = set()
        for error_line in error_lines:
            start = int(error_line) - 1
            while start >= 0 and lines[start].strip():  # Move up until an empty line
                lines_to_remove.add(start)
                start -= 1

            end = int(error_line) - 1
            while end < len(lines) and lines[end].strip():  # Move down until an empty line
                lines_to_remove.add(end)
                end += 1

        with open(sva_object.prop_location, 'w') as f:
            for i, line in enumerate(lines):
                if i not in lines_to_remove:
                    f.write(line)
    print('-----------Deleted lines around with errors from property module---------------\n')



# add syntax error free sva by Jasper to collection, feed to Jasper to run
def add_err_free_sva_collection(sva_object, err_free_sva_collection_path):
    with open(err_free_sva_collection_path, 'a+') as file:
        file.write(sva_object.sva)

# add the sva which passes Jasper to the collection
def add_useful_sva_collection(sva_object, useful_sva_collection_path):
    with open(useful_sva_collection_path, 'a+') as file:
        file.write(sva_object.sva)

# add the erroneous sva detected by Slang to the collection
def add_defect_sva_collection(sva_object, defect_sva_collection_path):
    with open(defect_sva_collection_path, 'a+') as file:
        file.write(sva_object.sva)

# add failed sva by Jasper to collection
def add_failed_sva_collection(sva_object, failed_sva_collection_path):
    with open(failed_sva_collection_path, 'a+') as file:
        file.write(sva_object.sva)

# Extract signal names from a YAML file.
"""def extract_signals_from_yaml(yaml_file):
    signal_list = []
    with open(yaml_file, "r") as file:
        data = yaml.safe_load(file)
        for entry in data:
            if "Signal name" not in entry:
                continue
            elif  "`" not in entry and "Signal name" in entry:
                signal_list.append(entry["Signal name"])
    return signal_list
    #return [entry["Signal name"] for entry in data  if "Signal name" in entry]"""

def extract_signals_from_yaml(yaml_file):
    signal_list = []
    with open(yaml_file, "r") as file:
        data = yaml.safe_load(file)
        for category in data.values():
            for entry in category:
                if "Signal name" in entry and "`" not in entry["Signal name"]:
                    signal_list.append(entry["Signal name"])
    return signal_list

# Generates a formal verification module declaration based on a SystemVerilog file and its signals.
def generate_Jaspergold_property_module(sva_obj, signal_list, module_property_file, index):
    import re

    original_module_name = sva_obj.module
    prop_module_name = f"{original_module_name}_prop"

    # Extract the module's ports
    port_section_match = re.search(r'\bmodule\s+\w+\s*\((.*?)\);', sva_obj.rtl_design, re.S)
    ports = port_section_match.group(1).strip() if port_section_match else ""

    # Extract import statements and parameters
    imports = re.findall(r'\bimport\s+[^;]+;', sva_obj.rtl_design)
    parameters = re.findall(r"parameter.*=.*", sva_obj.rtl_design)

    # Extract relevant signal declarations
    signal_definitions = []
    for signal in signal_list[:]:
        for line in sva_obj.rtl_design.split('\n'):
            if signal in line and '=' not in line:
                signal_declaration_regex = rf"^(?=.*\b(?:input|output|inout|logic|reg|wire|int|bit|::)\b).*\s*\w*\s*\b{signal}\b"
                signal_match = re.search(signal_declaration_regex, line)
                if signal_match:
                    line = line.split('//')[0].strip()
                    if not line:
                        break
                    line = line.replace(';', ',') if ';' in line else line
                    if not line.endswith(','):
                        line += ','
                    if 'automatic' in line:
                        line = line.replace('automatic', ' ')
                    if 'output' in line:
                        line = line.replace('output', 'input')
                    if not (line.lstrip().startswith("input") or line.lstrip().startswith("output") or line.lstrip().startswith("inout")):
                        line = 'input        ' + line.lstrip()
                    if line not in signal_definitions:
                        signal_definitions.append(line)
                    signal_list.remove(signal)
                    break

    if signal_definitions and signal_definitions[-1].endswith(','):
        signal_definitions[-1] = signal_definitions[-1].rstrip(',')

    # Start generating the property module
    generated_module = []

    # Header comment
    generated_module.append("// Auto-generated SystemVerilog Assertions (SVA)\n\n")

    # Imports (use your default or RTL-specific)
    generated_module.append("// Imported packages\n")
    generated_module.append("import ariane_pkg::*;\n")
    generated_module.append("import riscv::*;\n")
    generated_module.append("import std_cache_pkg::*;\n\n")

    # Module declaration
    generated_module.append(f"module {prop_module_name}\n")

    if parameters:
        generated_module.append("#(\n")
        generated_module.extend(f"    {param}\n" for param in parameters)
        generated_module.append(")\n")

    generated_module.append("(\n")
    for line in signal_definitions:
        generated_module.append(f"    {line}\n")
    generated_module.append(");\n\n")

    # Append the selected assertion
    generated_module.append(sva_obj.sva_list[index])
    generated_module.append("\n\nendmodule\n")

    # Write the final module
    with open(module_property_file, "w") as f:
        f.writelines(generated_module)

    print(f"✅ Generated module written to {module_property_file}.")


def create_files_for_jg(base_path, module_name, rtl_src_path, index):
    # files.vc content
    files_vc_content = f"""
--libext .v
--libext .h
--libext .sv
--libext .tmp.v
+incdir+${{DUT_PATH}}
-y ${{DUT_PATH}}
+incdir+${{SRC_PATH0}}
-y ${{SRC_PATH0}}
+incdir+${{INC_PATH}}
-y ${{INC_PATH}}
#-f ${{DUT_ROOT}}/Flist.ariane
-f ${{PROP_PATH}}/manual_sub.vc
${{INC_PATH}}/riscv_pkg.sv
${{SRC_PATH0}}/dm_pkg.sv
${{INC_PATH}}/ariane_pkg.sv
${{PROP_PATH}}/{module_name}_prop_{index}.sv
${{PROP_PATH}}/{module_name}_bind.sv
${{DUT_ROOT}}/src/{rtl_src_path}
${{INC_PATH}}/std_cache_pkg.sv
"""
    files_vc_file = os.path.join(base_path, "files_" + str(index) + ".vc")
    with open(files_vc_file, "w") as vc_file:
        vc_file.write(files_vc_content)
    print(f"Files.vc for sva id '{index}' created successfully at '{base_path}'!")


def create_jaspergold_structure(base_path, module_name, signal_list, rtl_src_path):
    """
    Creates a folder with a subfolder and files specific to the given module.

    :param base_path: The root directory where the folder structure should be created.
    :param module_name: The module name to replace placeholders in the file content.
    """
    if not os.path.exists(base_path):
        os.makedirs(base_path, exist_ok=True)
    fpv_module_file = os.path.join(base_path, f"fpv_{module_name}.tcl")
    manual_sub_file = os.path.join(base_path, "manual_sub.vc")
    binding_file= os.path.join(base_path, f"{module_name}_bind.sv")

    # test few signals
    #signal_list = extract_signals_from_yaml('signals/multiplier_signal_extractioncopy.yaml')
    # bind.sv content
    bind_module_connections = []
    for signal in signal_list:
        bind_module_connections.append(f"   .{signal}({module_name}.{signal})")
    connection_list =  ",\n".join(bind_module_connections)
    bind_content = f"""bind {module_name} {module_name}_prop
  #() u_{module_name}_sva(""" + connection_list + """);"""

    # fpv_module.tcl content
    fpv_module_content = f"""
# Set paths to DUT root and FT root (based on environment variables)
set ROOT [pwd]
set oneLevelUp [file dirname $ROOT]
set twoLevelUp [file dirname $oneLevelUp]
set threeLevelUp [file dirname $twoLevelUp]
set DUT_ROOT $threeLevelUp/ariane

# Analyze design under verification files (no edit)
set DUT_PATH  ${{DUT_ROOT}}/src
set SRC_PATH0 ${{DUT_ROOT}}/src/riscv-dbg/src
set INC_PATH ${{DUT_ROOT}}/include
set PROP_PATH ${{ROOT}}

check_cov -init -type all -model all
set_elaborate_single_run_mode off
set_automatic_library_search on
set_analyze_libunboundsearch on
set_analyze_librescan on
# Analyze property files
analyze -clear
analyze -sv12 -f ${{PROP_PATH}}/files_0.vc

# Elaborate design and properties
elaborate -top {module_name} -create_related_covers {{witness precondition}}
# Set up Clocks and Resets, for a clock and reset free environment, use 'clock -none' and 'reset -none'
clock clk_i
reset -expression (!rst_ni)

# Get design information to check general complexity
get_design_info

set_word_level_reduction on
set_prove_time_limit 72h

set_proofgrid_max_jobs 180
set_proofgrid_manager on
autoprove -all -bg -mem_limit 1024m
# Report proof results
report
check_cov -measure -type all
check_cov -report -report_file all_coverage.html -html -force
"""

    # manual_sub.vc content
    manual_sub_content = """
// Add here defines if needed
// Add here further dependencies not captured automatically
${INC_PATH}/riscv_pkg.sv
${SRC_PATH0}/dm_pkg.sv
${INC_PATH}/ariane_pkg.sv
${INC_PATH}/std_cache_pkg.sv

"""

    # Write the content to the respective files
    with open(fpv_module_file, "w") as fpv_file:
        fpv_file.write(fpv_module_content)
        print('----Created fpv .tcl file----', fpv_module_file)

    with open(manual_sub_file, "w") as manual_file:
        manual_file.write(manual_sub_content)

    with open(binding_file, 'w') as file:
        file.write(bind_content)

    print(f"Scripts and binding files for module '{module_name}' created successfully at '{base_path}'!")
