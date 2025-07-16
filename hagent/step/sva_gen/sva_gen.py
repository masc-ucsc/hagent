# README

# This program calls two functions to generate preconditions/post-conditions and assertions: generate_preconditions(signal, pre-condition_Input) and generate_assertions(signal, assertion_input).

# serval inputs to this program:
# verilog_lines: the rtl design code that we use to generate forward/backward slices and used as the input to LLM to generate pre-conditions and assertions
# parse_tree_text: the parser tree of the verilog_lines, used to construct the forward/backward slices for each signal in the module
# module_specification: the module specification used in the prompt to generate pre-conditions
# extracted_signals_path: the location of extracted signals .yaml file

# output of the program:
# output_precondition_file: generated pre-conditions and post-conditions from the function generate_preconditions(signal, pre-condition_Input)
# output_assertion_file: generated assertions from the function generate_assertions(signal, assertion_input)

# The xyz_mux_verilog_code and xyz_mux_parse_tree can be an easy example to help understand how to derive the coding slices from the text parser tree and RTL code. Basically it finds the node of the signal and related variables determined by the signal or determines the signal itself, and include the whole line into the forward/backward slices.

# To do
# 1. delete the last line in every tree-sitter parse tree file, as the backforward slice function reads the file from the last line, unlike forward slice function reading from the first line.

# model selection : o3-mini-2025-01-31, gpt-4o

import re
#from openai import OpenAI
import os
import tiktoken
import argparse
from hagent.step.sva_gen.sva_gen_prompts import assertion_prompt_rules
from queue import Queue
from hagent.step.sva_gen.fix_syntax_errors import extract_signals_from_yaml, create_files_for_jg, extract_errors, request_fix, write_back_fixed_sva, add_defect_sva_collection, generate_Jaspergold_property_module,  replace_assertions, create_jaspergold_structure, check_syntax_error_with_slang, delete_syntax_errors
from hagent.step.sva_gen.parse_jg_sva_log import jg_post_process
import subprocess
import time
import shutil
import threading
import signal
import sys
from hagent.core.llm_wrap import LLM_wrap
from hagent.core.llm_template import LLM_template
import yaml
from jinja2 import Template
_concurrency_semaphore = threading.Semaphore(8)


class sva:
    def __init__(self, signal, sva):
        self.signal = signal
        self.sva = sva
        self.module = ''
        self.err_free = False
        self.syntax_err = ''
        self.semantic_err = ''
        self.pass_verification = False
        self.fix_times = 0
        self.reveal_bugs = ''
        self.id = 0
        self.prop_location = []
        self.prompt_history = ''
        self.rtl_design = '' # the content of the rtl design
        self.sva_list = None
        self.pass_count = 0
        self.fail_count = 0
        self.proven_count = 0
        self.cex_count = 0



# -------------------- ✅ Setup Section (Updated) --------------------

# Argument parsing
def parse_arguments():
    parser = argparse.ArgumentParser(description="Generate preconditions and assertions for signals in RTL design.")
    parser.add_argument("io_config", type=str, help="Path to YAML config for input/output file paths")
    parser.add_argument("llm_conf", type=str, help="Path to LLM config YAML")
    return parser.parse_args()

# File and YAML utilities
def read_file(file_path):
    if not os.path.isfile(file_path):
        print(f"[❌ ERROR] File not found: {file_path}")
        sys.exit(1)
    with open(file_path, 'r') as file:
        return file.read()

def read_yaml(path):
    if not os.path.isfile(path):
        print(f"[❌ ERROR] YAML config not found: {path}")
        sys.exit(1)
    with open(path, 'r') as f:
        return yaml.safe_load(f)

# -------- Start Setup --------
args = parse_arguments()
io_config = read_yaml(args.io_config)
log_file = io_config["llm_log_file"]
# Output paths
output_precondition_file = io_config["output_precondition_file"]
output_assertion_file = io_config["output_assertion_file"]
jg_assertion_file = io_config["jg_assertion_file"]


# Paths from config
module_spec_path = io_config.get("module_spec")
verilog_code_file = io_config["verilog_code_file"]
parse_tree_path = io_config.get("parse_tree")
extracted_signals_path = io_config["extracted_signals"]

# Flags for optional inputs
module_spec_flag = module_spec_path and module_spec_path.lower() != 'none'
parsetree_flag = parse_tree_path and parse_tree_path.lower() != 'none'

# Read input contents
module_specification = read_file(module_spec_path) if module_spec_flag else ''
verilog_lines = read_file(verilog_code_file)
parse_tree_text = read_file(parse_tree_path) if parsetree_flag else ''

# Extract module name and RTL source root
match = re.search(r"([^/]+)\.sv$", verilog_code_file)
rtl_module = match.group(1) if match else 'unknown'

rtl_src_path = re.search(r"(?<=src/).*", verilog_code_file)
rtl_src_path = rtl_src_path.group() if rtl_src_path else verilog_code_file




# Ensure output directories exist
for path in [output_precondition_file, output_assertion_file, jg_assertion_file, log_file]:
    dir_path = os.path.dirname(path)
    if dir_path:  # Avoid os.makedirs('') error
        os.makedirs(dir_path, exist_ok=True)

# Initialize LLM and templates
llm = LLM_wrap(name="default", conf_file=args.llm_conf, log_file=io_config["llm_log_file"])
template_dict = LLM_template(args.llm_conf).template_dict       

# ✅ Debug info
print('✅ Loaded config and files')
print(f"📂 Module Name Detected: {rtl_module}")
print(f"📁 RTL Source Path: {rtl_src_path}")
print(f"🧾 Using Spec File: {module_spec_path if module_spec_flag else 'None'}")
print(f"🌳 Parse Tree Provided: {parse_tree_path if parsetree_flag else 'None'}")
print(f"📌 Extracted Signals YAML: {extracted_signals_path}")

print('📏 Verilog line count:', verilog_lines.count('\n'))



#print('length of verilog lines: ', verilog_lines.count('\n'), '\n')
#print(parse_tree_text.splitlines()[0])

def remove_empty_lines(text):
    lines = text.split('\n')
    non_empty_lines = [line for line in lines if line.strip() != '']
    return '\n'.join(non_empty_lines)

# Define a function to parse the tree from the text
def parse_tree_from_text(parse_tree_text):
    lines = parse_tree_text.strip().split('\n')
    root_node = None
    stack = []

    for line in lines:
        indent = len(line) - len(line.lstrip(' '))
        points = re.findall(r'\[(\d+), (\d+)\]', line)
        if len(points) < 2:
            continue
        start_point = tuple(map(int, points[0]))
        end_point = tuple(map(int, points[1]))
        node = {
            'type': line.strip().split(' ')[0][1:],
            'start_point': start_point,
            'end_point': end_point,
            'children': [],
            'parent': None
        }
        while stack and stack[-1]['indent'] >= indent:
            stack.pop()
        if stack:
            parent = stack[-1]['node']
            parent['children'].append(node)
            node['parent'] = parent
        stack.append({'indent': indent, 'node': node})
        if indent == 0:
            root_node = node

    return root_node

# Function to print the parsed tree (for debugging purposes)
def print_tree(node, indent=0):
    print(' ' * indent + f"{node['type']} {node['start_point']} - {node['end_point']}")
    for child in node['children']:
        print_tree(child, indent + 2)

# Parse the tree from the text
#root_node = parse_tree_from_text(parse_tree_text)

# Function to extract code under a tree node and all its children
def extract_code_from_node(node, verilog_lines):
    lines = []
    def gather_lines(n):
        start_byte = n['start_point']
        end_byte = n['end_point']
        start_line, start_col = start_byte
        end_line, end_col = end_byte
        if start_line == end_line:
            lines.append(verilog_lines[start_line].strip())
        else:
            lines.append(verilog_lines[start_line][start_col:].strip())
            for line in range(start_line + 1, end_line):
                lines.append(verilog_lines[line].strip())
            lines.append(verilog_lines[end_line][:end_col].strip())
        for child in n['children']:
            gather_lines(child)
    gather_lines(node)
    return '\n'.join(lines)

# Function to find forward slice of a signal
def find_forward_slice(node, signal_name, verilog_lines):
    slice_lines = set()

    start_byte = node['start_point']
    end_byte = node['end_point']
    start_line, start_col = start_byte
    end_line, end_col = end_byte
    if start_line == end_line:
        code_line = verilog_lines[start_line].strip()
    else:

        for line in verilog_lines:
            if re.search( r'\b' + re.escape(signal_name) + r'\b', line):
                slice_lines.add(line )
    #print(slice_lines)

    return slice_lines



# Define a function to extract the full line of code using the parse tree
def extract_full_line_from_tree(node, verilog_lines):
    start_byte = node['start_point']
    end_byte = node['end_point']
    start_line, start_col = start_byte
    end_line, end_col = end_byte
    if start_line == end_line:
        return verilog_lines[start_line ].strip()
    lines = [verilog_lines[start_line][start_col:].strip()]
    for line in range(start_line + 1, end_line):
        lines.append(verilog_lines[line].strip())
    lines.append(verilog_lines[end_line][:end_col].strip())
    return ' '.join(lines)


# Example: Extract forward slice for a specific signal
def find_signal_node(root, signal_name, verilog_lines):
    result = []
    def traverse(node):
        if node['type'] == 'simple_identifier' and verilog_lines[node['start_point'][0] ][node['start_point'][1]:node['end_point'][1]] == signal_name:
            slice_line = extract_full_line_from_tree(node, verilog_lines)
            #print(slice_line)
            result.append(slice_line)
        for child in node['children']:
            traverse(child)
    traverse(root)
    return result

def get_index_for_forward_slices(node):
    # find the node of the if conditional statement
    while node is not None and node['type'] != "conditional_statement": 
        node = node['parent']
    #if node is None:
    #    return []
    #forward_indices = [node['start_point'][0]]  # Include the current node's start point
    start_points = []
    if node and node['children']:
        for child in node['children']:
            if child['start_point'][0] != child['end_point'][0]:
                for i in range(child['start_point'][0], child['end_point'][0]):
                    if i not in start_points:
                        start_points.append(i)
            else:
                if child['start_point'][0] not in start_points:
                    start_points.append(child['start_point'][0])
    return (start_points)  # Convert set to list before returning


def forward_find_parent_node(node, forward_slice_index):
    if(node['parent']):
        parent = node['parent']
        if( parent['start_point'][0] == node['start_point'][0]):
            if(parent['type'] != 'variable_lvalue' and parent['type'] != 'net_lvalue'):
                if(parent['type'] == 'net_assignment' or
                    parent['type'] == 'operator_assignment' or
                    parent['type'] == 'nonblocking_assignment' or
                    parent['type'] == 'blocking_assignment' or
                    parent['type'] == 'conditional_statement' or      # add if conditional statement to forward slices
                    parent['type'] == 'case_expression'):     # add case statement to forward slices
                    #print('----------- parent node type in forward slices: ', parent['type'], '\n')
                    # add all the lines of if end block to the forward slices
                    if parent['type'] == 'conditional_statement':
                        #print('*******find the conditional statement node start point*************')
                        #parent_of_conditional_statement = parent['parent']
                        for i in range(parent['start_point'][0], parent['end_point'][0]):
                            if i not in forward_slice_index:
                                forward_slice_index.append(i)
                            # add the last line end of the if block to forward slices
                        forward_slice_index.append(parent['end_point'][0]+1)
                    if((node['start_point'][0]) not in forward_slice_index):
                        forward_slice_index.append(node['start_point'][0])
                        #print(forward_slice_index)
                        return parent
                else:
                    if (parent['parent']):
                       return forward_find_parent_node(node['parent'], forward_slice_index)
            else:
                exit
        else:
           return None
    else:
        return None



# Function to find the node corresponding to a specific line
def find_node_for_line(root, line_num):
    def traverse(node):
        start_line = node['start_point'][0]
        end_line = node['end_point'][0]
        if start_line == line_num and line_num == end_line:
            return node
        elif start_line <= line_num and line_num <= end_line:
            for child in node['children']:
                result = traverse(child)
                if result:
                    return result
            return None
        return None

    return traverse(root)



def forward_slice(root_node, signal_name, verilog_lines, var_list):
    current_line = 0
    last_line = root_node['end_point'][0]
    var_list.append(signal_name)
    forward_slice_index = []

    # for item in verilog_lines:
    def traverse(node, signal_in_the_list):
        if(node and node['type'] != 'ERROR'):
            #print(node['start_point'][0]+1, node['start_point'][1], node['end_point'][1], verilog_lines[node['start_point'][0] ][node['start_point'][1]:node['end_point'][1]], node['type'], '^^^^^', signal_in_the_list)

            #if(verilog_lines[node['start_point'][0]+1 ][node['start_point'][1]:node['end_point'][1]] == signal_in_the_list and node['type'] != 'net_lvalue' and node['type'] != 'variable_lvalue' and node['parent']['type'] != 'net_lvalue' and node['parent']['type'] != 'variable_lvalue'):
            if(verilog_lines[node['start_point'][0] ][node['start_point'][1]:node['end_point'][1]] == signal_in_the_list and node['parent']['type'] != 'net_lvalue' and node['parent']['type'] != 'variable_lvalue'):

                #print('!!!!!!!!!!!', verilog_lines[node['start_point'][0]])
                # if we find the signal to be in this line, start from this node and check the following conditions
                # find if father node contains assignment node types
                # if node.father.father.father == net-assignment && node.father.father.father.child == net_lvalue, add net_lvalue.children to the list
                # if node.father.father.father.father == assignment_operator && assignment_operator.father == operator_assignment, add operator_assignment.children to the list
                # find out the first operator_assignment father node
                # father node != lvalue
                #print("found signal a!", verilog_lines[node['start_point'][0] ][node['start_point'][1]:node['end_point'][1]])
                parent_node = forward_find_parent_node(node, forward_slice_index)
                # find out the variables that are affected by this signal under its parent node, add them in the var_list
                if(parent_node):
                    for child in parent_node['children']:
                        if child['type'] == 'variable_lvalue' or child['type'] == 'net_lvalue':
                            # single var assignment
                            if(len(child['children']) == 1):
                                child_node = child['children'][0]
                                if(child_node['type'] == 'simple_identifier'):
                                    if(verilog_lines[child_node['start_point'][0]+1 ][child_node['start_point'][1]:child_node['end_point'][1]] not in var_list):
                                        var_list.append(verilog_lines[child_node['start_point'][0]+1 ][child_node['start_point'][1]:child_node['end_point'][1]])

                                    # concatenation case
            else: # if we find the signal not in this line, line number += 1, node -> child
                for child in node['children']:
                    traverse(child, signal_in_the_list)
                    #print("we're at: ", current_line, verilog_lines[child['start_point'][0]][child['start_point'][1]:child['end_point'][1]])

    while (current_line <= last_line):
        # find the root node of the current line
        current_node = find_node_for_line(root_node, current_line)
        if(current_node):
            for signal in var_list:
                traverse(current_node, signal)
                #print('-------', signal, current_line, last_line, var_list)
        current_line += 1

    #for signal in var_list:
     #   print(signal)

    return forward_slice_index


def backward_find_parent_node(node, backward_slice_index):
    if(node['parent']):
        parent = node['parent']
        if( parent['type'] == 'variable_lvalue' or parent['type'] == 'net_lvalue'):
            assignment_node = parent['parent']
            # all the lvalues shoud be on the same line
            if(assignment_node and assignment_node['start_point'][0] == parent['start_point'][0] and (assignment_node['type'] == 'net_assignment' or assignment_node['type'] == 'operator_assignment' or assignment_node['type'] == 'nonblocking_assignment')):
                backward_slice_index.append(assignment_node['start_point'][0])
                #print(backward_slice_index)
                return assignment_node
        else:
            return backward_find_parent_node(parent, backward_slice_index)
    else:
        return None


def backward_slice(root_node, signal_name, verilog_lines, var_list):
    current_line = root_node['end_point'][0]
    var_list.append(signal_name)
    backward_slice_index = []

    def traverse(node, signal_in_the_list):
        if(node):
            #print(node['start_point'][0]+1, node['start_point'][1], node['end_point'][1], verilog_lines[node['start_point'][0] ][node['start_point'][1]:node['end_point'][1]], node['type'], '^^^^^', signal_in_the_list)

            if(verilog_lines[node['start_point'][0]][node['start_point'][1]:node['end_point'][1]] == signal_in_the_list and node['type'] == 'simple_identifier'):
                #print('!!!!!!!!!!', verilog_lines[node['start_point'][0]+1][node['start_point'][1]:node['end_point'][1]])
                # if we find the signal to be in this line, start from this node and check the following conditions
                # find if father node is net_lvalue or variable_lvalue
                # check if parent's parent node is assignment type
                # add all the variables on the right side of the assignment to the list
                parent_assignment_node = backward_find_parent_node(node, backward_slice_index)
                # find out the variables that contribute to the assignment of this signal, add them in the var_list
                if(parent_assignment_node):
                    for child in parent_assignment_node['children']:
                        if child['type'] != 'variable_lvalue' and child['type'] != 'net_lvalue':

                            def find_var_node(child):
                                if (child):
                                    if (child['type'] == 'simple_identifier' and verilog_lines[child['start_point'][0]+1][child['start_point'][1]:child['end_point'][1]] not in var_list):
                                        var_list.append(verilog_lines[child['start_point'][0]+1][child['start_point'][1]:child['end_point'][1]])
                                    else:
                                        if(child['children']):
                                            for child_node in child['children']:
                                                find_var_node(child_node)
                                        else:
                                            exit

                            find_var_node(child)
            else: # if we find the signal not in this line, line number += 1, node -> child
                for child in node['children']:
                    traverse(child, signal_in_the_list)
                    #print("we're at: ", current_line, verilog_lines[child['start_point'][0]][child['start_point'][1]:child['end_point'][1]])

    while (current_line >= 0):
        # find the root node of the current line
        current_node = find_node_for_line(root_node, current_line)
        if(current_node):
            for signal in var_list:
                traverse(current_node, signal)
                #print('-------', signal, current_line, var_list)
        current_line -= 1

    #print('the signal is: ', signal_name, 'signals in the backward slices: ')
    #for signal in var_list:
     #   print(signal)

    return backward_slice_index


def forward_backward_slices(root_node, signal_name, verilog_lines):
    verilog_lines = verilog_lines.splitlines()
    signal_slices = []
    forward_var_list = []
    forward_slice_index = forward_slice(root_node, signal_name, verilog_lines, forward_var_list)
    #print('------forward slices for the signal ', signal_name, ' are ------- ')
    for i in forward_slice_index:
        #print(verilog_lines[i])
        signal_slices.append(verilog_lines[i])

    backward_var_list = []
    backward_slice_index = backward_slice(root_node, signal_name, verilog_lines, backward_var_list)
    #print('------backward slices for the signal ', signal_name, ' are ------- ')
    for i in backward_slice_index:
        #print(verilog_lines[i])
        if i not in forward_slice_index:        # remove duplicate lines of forward slices
            signal_slices.append(verilog_lines[i])
    
    return signal_slices

#forward_backward_slices(root_node, signal_name, verilog_lines)


systemInput_precondition = "You are a professional VLSI specification and RTL code analyzer. When I ask for information on an input, output or internal register and logic signal, please extract all the pre-conditions and post-conditions related to this signal in the RTL code.\
     You can also analyze the specification file and code slices in the RTL code to extract the information. Note that the extracted information should be suitable for the SystemVerilog Assertions (SVAs) generation, and output all the information in the following format:\
[Signal name]: name in RTL code\
 [Definition]: bit-width and signal type (in/out/register), etc\
 [Functionality]: all the function information illustrated in SPEC and RTL code\
 [Interconnection]: the relationship with all other signals\
 [Additional information]: all other related information\
[Related Signals]: names of all other signals mentioned in the Description part.\
[pre-condition]: the operatoins that must be true to continue the assertion evaluation of the signal. \
[post-condition]: the operatoins that must be true after the assertion evaluation of the signal has finished."

systemInput_assertion = "You are a professional VLSI specification and RTL code analyzer. When I ask you to generate assertion for signals like input, output or internal register and logic signal, output all the content in the following format:\
[Signal name]: name in RTL code\
[Immediate Assertion]: a procedural statement, and is non-temporal.\
[Concurrent Assertion]: detects behavior over time.\
"

#def generate_preconditions(signal, precondition_Input, model):

from jinja2 import Template

def render_prompt(template_list, context):
    """Render a list of LLM messages using Jinja2 and context."""
    rendered = []
    for item in template_list:
        tmpl = Template(item["content"])
        rendered.append({
            "role": item["role"],
            "content": tmpl.render(context=context)
        })
    return rendered

from jinja2 import Template

from jinja2 import Template

def sanitize_context_dict(context_dict):
    """Ensure all values in context_dict are strings or safely converted."""
    for key, value in context_dict.items():
        if isinstance(value, list):
            context_dict[key] = "\n".join(str(v) for v in value)
        elif value is None:
            context_dict[key] = ""
        else:
            context_dict[key] = str(value)
    return context_dict


from jinja2 import Template

def generate_preconditions(signal, prompt_input, llm, template_dict, output_precondition_file):
    if "default" not in template_dict or "precondition" not in template_dict["default"]:
        print("[ERROR] Missing precondition template in config.")
        return None

    context_dict = {
        "signal_name": signal,
        "rtl_full": prompt_input.get("rtl_full", "// RTL code not provided."),
        "spec": prompt_input.get("spec", "// Specification not available."),
        "signal_slices": "\n".join(prompt_input.get("signal_slices", [])),
        "signal_type": prompt_input.get("signal_types", {}).get(signal, "unknown"),
    }

    #print(f"[DEBUG] Injected precondition prompt context for `{signal}`:\n{context_dict}")

    result = llm.inference(context_dict, prompt_index="precondition")

    if llm.last_error:
        print(f"❌ LLM Error for `{signal}`:", llm.last_error)
        return None

    if not result or not result[0].strip():
        print(f"[WARNING] No precondition output for `{signal}`.")
        return None

    with open(output_precondition_file, "a") as f:
        f.write(f"\n##### For the signal {signal}, these are the preconditions generated:\n{result[0]}\n")

    return result[0]



def generate_assertions(signal, precondition_output, prompt_input, llm, template_dict, output_assertion_file):
    if not precondition_output:
        print(f"[SKIP] Missing precondition output for `{signal}`.")
        return None

    if "default" not in template_dict or "assertion" not in template_dict["default"]:
        print("[ERROR] Missing assertion template in config.")
        return None

    context_dict = {
        "signal_name": signal,
        "rtl_full": prompt_input.get("rtl_full", "// Not provided."),
        "spec": prompt_input.get("spec", "// Not provided."),
        "signal_slices": "\n".join(prompt_input.get("signal_slices", [])),
        "precondition_output": precondition_output,
    }

    #print(f"[DEBUG] Injected assertion prompt context for `{signal}`:\n{context_dict}")

    result = llm.inference(context_dict, prompt_index="assertion")

    if llm.last_error:
        print(f"❌ LLM Error for assertion `{signal}`:", llm.last_error)
        return None

    if not result or not result[0].strip():
        print(f"[WARNING] No assertion output for `{signal}`.")
        return None

    with open(output_assertion_file, "a") as f:
        f.write(f"\n##### For the signal {signal}, these are the assertions generated:\n{result[0]}\n")

    return result[0]




# generate pre-conditions and assertions for rach signal in the signal list .yaml file
def main_call(output_assertion_file):
    import re, os
    from queue import Queue

    signal_list = []
    pattern = r'"([^"]+)"'

    # Extract signal names, skip clock/reset/invalids
    with open(extracted_signals_path, 'r') as file:
        for line in file:
            matches = re.findall(pattern, line)
            if matches:
                sig = matches[0]
                if any(x in sig.lower() for x in ['clk', 'clock', 'rst', 'reset', 'none']):
                    continue
                if re.match(r".*/.*", sig):
                    continue
                signal_list.append(sig)

    print('Extracted signal count:', len(signal_list))
    print('Signal list:', signal_list)

    # Get RTL parse tree root
    root_node = parse_tree_from_text(parse_tree_text)

    for signal in signal_list:
        signal_slices = []
        if parsetree_flag:
            signal_slices = forward_backward_slices(root_node, signal, verilog_lines)

            print(f"🔍 Slices for `{signal}`:", signal_slices)

        # Prepare prompt input for precondition generation
        prompt_context = {
            "signal_name": signal,
            "signal_slices": signal_slices,
            "rtl_full": verilog_lines,
            "spec": module_specification if module_spec_flag else "// No spec available.",
            "metadata": {
                "name": signal,
                "type": "logic [riscv::XLEN-1:0] (inferred)",
                "role": "internal signal used in ALU logic",
                "description": "Involved in shift operation chains and result propagation."
            }
        }

        # Generate preconditions
        precondition_output = generate_preconditions(signal, prompt_context, llm, template_dict, output_precondition_file)

        if not precondition_output or "please provide the context" in precondition_output.lower():
            print(f"[ERROR] LLM returned invalid output for signal `{signal}`")
            continue

        # Prepare input for assertion generation
        assertion_context = {
            "signal_name": signal,
            "precondition_output": precondition_output,
            "rtl_full": verilog_lines,
            "signal_slices": signal_slices,
            "spec": module_specification
        }

        # Generate assertions
        sva_response = generate_assertions(signal, precondition_output, assertion_context, llm, template_dict, output_assertion_file)

        if not sva_response:
            print(f"⚠️ No valid SVAs for `{signal}`.")
            continue

        print(f"✅ Assertion generated for `{signal}`.")

        # Temp write for extracting blocks
        with open('assertions_temp.txt', 'w') as f:
            f.write(sva_response)

        sva_block = extract_property_blocks('assertions_temp.txt')
        os.remove('assertions_temp.txt')

        sva_list = extract_sva_blocks(" ".join(sva_block))
        sva_block_lines = [line for code in sva_block for line in code.split('\n')]

        if not sva_list:
            print(f"⚠️ No valid SVA blocks found for `{signal}`.")
            continue

        # Build and enqueue SVA object
        sva_instance = sva(signal, sva_block_lines)
        sva_instance.sva_list = sva_list
        sva_instance.prompt_history += precondition_output
        sva_instance.module = rtl_module
        sva_instance.rtl_design = verilog_lines
        log(sva_instance)
        sva_queue.put(sva_instance)




def extract_sva_blocks(code_block):
    assertions = []
    lines = code_block.split('\n')
    current_comment = []
    current_assertion = []
    collecting_assertion = False
    
    for line in lines:
        stripped_line = line.strip()
        
        if stripped_line.startswith('//'):
            if not collecting_assertion:
                current_comment.append(stripped_line)
        elif 'assert property' in stripped_line:
            current_assertion.append(stripped_line)
            collecting_assertion = True
        elif collecting_assertion:
            if stripped_line == "":  # Stop collecting when an empty line is encountered
                assertions.append(('\n'.join(current_comment), '\n'.join(current_assertion)))
                current_comment = []
                current_assertion = []
                collecting_assertion = False
            else:
                current_assertion.append(stripped_line)
    
    if current_assertion:  # Capture the last assertion if there's no empty line at the end
        assertions.append(('\n'.join(current_comment), '\n'.join(current_assertion)))
    
    return ['\n'.join([comment, assertion]) for comment, assertion in assertions]


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

    sva_block = []
    for line in result:
        if '// assertions/property above' in line:
            line = line.replace('// assertions/property above', '')
        if '// assertions/property below' in line:
            line = line.replace('// assertions/property below', '')
        sva_block.append(line)

    return sva_block

def sva_write(output_assertion_file, jg_assertion_file):
    if not os.path.exists(output_assertion_file):
        print(f"[WARNING] No assertions written. Skipping extract for `{output_assertion_file}`.")
        return

    blocks = extract_property_blocks(output_assertion_file)

    with open(jg_assertion_file, "a+") as file:
        file.writelines(blocks)

def sva_write_process(output_sva_file, jg_sva_file, sva_queue):
    main_call(output_sva_file)
    sva_write(output_sva_file, jg_sva_file)

def log(sva_instance):
    if not os.path.exists('gpt_logs'):
        os.makedirs('gpt_logs', exist_ok=True)
    log_file = 'gpt_logs/' + sva_instance.module + '_prompt_response_logs.txt'
    with open(log_file, 'a+') as file:
        file.write(sva_instance.prompt_history)

def check_status_from_jasper_output(std_output):
    # Define the regex patterns to identify key parts of the SUMMARY section

    error_pattern = r"ERROR \(([A-Z]{3}[A-Z])(\d+)\): (\d+) errors detected in the design file\(s\)\."
    # Flags to track whether we find all expected keyword from std output
    found_no_errors = False
    # Process each line
    output_lines = std_output
    for line in output_lines:
        # Check for the "error" line showing no errors
        if re.match(error_pattern, line):
            found_no_errors = True
            print('match error in the output\n')
    # end the process
    if(found_no_errors):
        return False
    else:
        return True

def update_tcl_files(jg_path, old_index, new_index, module_name):
    files_vc_path = os.path.join(jg_path, 'files_' + str(old_index) + '.vc')
    tcl_path = os.path.join(jg_path, f"fpv_{module_name}.tcl")
     
     # replace the id in files.vc in tcl script
    with open(tcl_path, 'r') as file:
       tcl_content = file.read()
    
    updated_tcl_content = re.sub(f'files_{old_index}.vc', f'files_{new_index}.vc', tcl_content)
    print('-----Updated tcl content---------- ')
    with open(tcl_path, 'w') as file:
        file.write(updated_tcl_content)

     # replace the id in prop.sv in files.vc
    with open(files_vc_path, 'r') as file:
       files_content = file.read()
    
    updated_files_content = re.sub(r'prop_\d+\.sv', f'prop_{new_index}.sv', files_content)
    
    with open(files_vc_path, 'w') as file:
        file.write(updated_files_content)

# given the property module sv path, run in jasper
def run_JasperGold(sva_object, jg_path):
    # -acquire_proj to acquire the ownership of the project
    print('Ready to run Jasper\n')
    print("There are '{}' property modules\n".format(len(sva_object.sva_list)+1))
    for i in range(len(sva_object.sva_list)):
        if i == 0:
            update_tcl_files(jg_path, 0, 0, sva_object.module)
        elif i > 0:
            update_tcl_files(jg_path, i-1, i, sva_object.module)
        sva_object.fix_times = 0
        print('Execute Jasper for the ', i, 'th property sv file.\n')
        command = f'cd ' + jg_path + ' && jg -no_gui -allow_unsupported_OS -acquire_proj fpv_' + sva_object.module + '.tcl -proj ' + jg_path + ' &'
        #print(command)
        #tcl_command = f"jg -command 'include " + jg_path + "fpv_" + sva_object.module + ".tcl'"
        with _concurrency_semaphore:
            # Start subprocess in a new process group to facilitate group termination.
            jg_process = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, preexec_fn=os.setsid,shell=True, text=True )

            # Track if the log file has stabilized
            start_time = time.time()
            last_output_time = time.time()
            inactivity_timeout=10
            process_timeout = 100
            err_pattern = r'ERROR \(ENL\d+\): \d+ errors detected in the design file\(s\)\.'
            jg_log_path = os.path.join(jg_path, 'jg_proj/', sva_object.module, 'sva/jg.log')

            # detect if the sva passes the Jasper
            try:
                stdout, stderr = jg_process.communicate()
                if stderr:
                    print(f'Error of Jasper process: {stderr}')
                if stdout:
                    print(f'STD of Jasper process: {stdout}')
                while True:
                    if os.path.exists(jg_log_path):
                        print('find jasper log\n')
                        with open(jg_log_path, 'r') as file:
                            log = file.read()
                            match = re.search(err_pattern, log)
                            file.close()
                            # there may not be 'syntax error' in the stdout
                            if match:
                                print('********Found syntax errors from the jasper log********\n')
                                while(sva_object.fix_times <= 5):
                                    #send request to OpenAI API to fix the syntax error raised by jasper gold
                                    error_message = extract_errors(jg_log_path, 0)
                                    assertion_fix_temp_file = os.path.join(jg_path + 'assertion_fix_temp.sv')
                                    #request_fix(error_message, sva_object, model, i)
                                    request_fix(error_message, sva_object, i, llm)
                                    sva_object.fix_times  += 1
                                    print('Send the syntax errors to LLM to fix for the ', sva_object.fix_times, ' time for the signal ' + sva_object.signal + ' with Jasper error message.\n')                                
                                    process = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, preexec_fn=os.setsid,shell=True, text=True )
                                    stdout, stderr = process.communicate()
                                    if stderr:
                                        print(stderr)
                                    if stdout:
                                        print(stdout)
                                    with open(jg_log_path, 'r') as file:
                                        log = file.read()
                                        err_match = re.search(err_pattern, log)
                                        file.close()
                                    if not err_match:
                                        #sva_object.err_free = True
                                        print(f'------------Fixed the errors after {sva_object.fix_times} times interacting with LLM----------------\n')
                                        print('-------------Compiled assertion +1 --------------------')
                                        post_process(jg_path, sva_object, sva_object.sva_list[i], True)
                                        break
                                if sva_object.fix_times > 5:
                                    print(':::::::::::fix times > 5\n')             
                                    post_process(jg_path, sva_object, sva_object.sva_list[i], False)

                            elif 'error' in stdout.strip() and sva_object.fix_times > 5:
                                print('-------------Failed assertion +1 --------------------')
                                #delete_syntax_errors(jg_log_path, sva_object) 
                                post_process(jg_path, sva_object, sva_object.sva_list[i], False)
                                break
                            else:
                                print('Did not find errors from jasper log\n')
                            proven_match = re.search(r'- proven\s+:\s+1\s+\(100%\)', log)
                            cex_match = re.search(r'- cex\s+:\s+1\s+\(100%\)', log)
                            if proven_match:
                                sva_object.proven_count += 1
                                with open('sva/proven.sv', 'a') as file:
                                    file.write(str(sva_object.sva_list[i]))
                                print('************************************ Proven sva + 1************************************\n')
                            if cex_match: 
                                sva_object.cex_count += 1
                                with open('sva/cex.sv', 'a') as file:
                                    file.write(str(sva_object.sva_list[i]))
                                print('************************************ CEX sva + 1************************************\n')
                                break
                    else:
                        last_output_time = time.time()
                        time_since_last_output = time.time() - last_output_time
                        if time_since_last_output > inactivity_timeout:
                            print(f"No output for {inactivity_timeout} seconds. Assuming process is done.")
                            #os.killpg(os.getpgid(jg_process.pid), signal.SIGKILL)
                            break
                    if jg_process.poll() is not None:
                        print("Process has terminated.")
                        break
            except KeyboardInterrupt:
                print("Japser Gold process interrupted by user.")
                os.killpg(os.getpgid(jg_process.pid), signal.SIGKILL)

        #useful_properties, failed_properties = post_process(jg_path, sva_object.sva_list[i])
    #return useful_properties, failed_properties

def post_process(jg_path, sva_object, sva_item, pass_flag):
    jg_log_path = os.path.join(jg_path, 'jg_proj/', sva_object.module, 'sva/jg.log')
    if not os.path.exists('sva/'):
        os.mkdir('sva/')
    if pass_flag:
        sva_object.pass_count += 1
        err_free_sva_collection_path= os.path.join('sva', 'err_free_sva_collection.sv')
        with open(err_free_sva_collection_path, 'a+') as file:
            file.write(sva_item)
            file.write('\n')
    else:
        sva_object.fail_count += 1
        false_sva_collection_path= os.path.join('sva', 'false_sva_collection.sv')
        with open(false_sva_collection_path, 'a+') as file:
            file.write(sva_item)
            file.write('\n')



def send_command_to_jasper(process, command):
    #if process.poll() is None:  # Check if process is still running
    print(f"Sending command: {command} to Jasper")
    process.stdin.write(command + "\n")
    process.stdin.flush()  # Ensure the command is sent immediately
#else:
    #    print("JasperGold process is no longer running.")

def generate_slices():
    # the extracted signal list of the module
    signal_list = []
    pattern = r'\"([^\"]+)\"'

    with open(extracted_signals_path, 'r') as file:
        content = file.readlines()
        for line in content:
            matches = re.findall(pattern, line)
            if(matches):
                if('clk' in matches[0] or 'clock' in matches[0] or 'rst' in matches[0] or 'reset' in matches[0] or 'none' in matches[0] or 'None' in matches[0]):
                    continue
                if(re.match(r".*/.*", matches[0])):
                    continue
                else:
                    signal_list.append(matches[0])

    print('the extracted signal list of the module: ', len(signal_list), '\n')
    print('signal list: ', signal_list)

    # Parse the tree from the text
    root_node = parse_tree_from_text(parse_tree_text)
    #print('&&&&&&&&&&&&&&&&&&&', root_node['type'], verilog_lines[root_node['start_point'][0]+1][root_node['start_point'][1]:root_node['end_point'][1]])
    for signal in signal_list:
        signal_slices = forward_backward_slices(root_node, signal, verilog_lines)
        print('signal slices for {}: '.format(signal), signal_slices)

def find_signal_yaml(sva_module, search_root):
    filename = sva_module + '_signal_extraction.yaml'
    for root, _, files in os.walk(search_root):
        if filename in files:
            return os.path.join(root, filename)
    return None

# Main Execution Block
if __name__ == '__main__':
    useful_sva = 0
    failed_sva = 0
    sva_queue = Queue(maxsize=1000)
    sva_write_process(output_assertion_file, jg_assertion_file, sva_queue)

    print('-------Done with generating SVAs, start to create Jasper directory and running-------\n')
    sva_queue_counter = sva_queue.qsize()
    processed_svas = []

    while not sva_queue.empty():
        print(f'-------------------{sva_queue.qsize()} objects are in the sva queue currently.-----------------------')
        sva_obj = sva_queue.get()

        if not sva_obj.sva_list:
            print(f"⚠️ Skipping signal '{sva_obj.signal}' — No SVAs generated.\n")
            continue

        print("the sva instance's sva is: " + str(sva_obj.sva) + '\n')
        sva_obj.id = sva_queue_counter - sva_queue.qsize()
        sva_module = sva_obj.module
        #signal_yaml_file = 'signals/' + sva_module + '_signal_extraction.yaml'
        # Get the root path for YAML search from config
        yaml_search_root = io_config.get("signal_yaml_search_root", ".")

        # Flexible search for YAML file
        signal_yaml_file = find_signal_yaml(sva_module, yaml_search_root)
        if not signal_yaml_file or not os.path.exists(signal_yaml_file):
            print(f"[ERROR] Signal YAML not found for module `{sva_module}` in `{yaml_search_root}`")
            continue
        
        
        jg_path = 'jg_proj/' + sva_module + '/sva/'

        signal_list = extract_signals_from_yaml(signal_yaml_file)
        create_jaspergold_structure(jg_path, sva_module, signal_list, rtl_src_path)
        if not os.path.exists(jg_path):
            os.makedirs(jg_path, exist_ok=True)

        for i in range(len(sva_obj.sva_list)):
            prop_file = jg_path + sva_module + '_prop_' + str(i) + '.sv'
            sva_obj.prop_location.append(prop_file)
            signal_list = extract_signals_from_yaml(signal_yaml_file)
            generate_Jaspergold_property_module(sva_obj, signal_list, prop_file, i)
            create_files_for_jg(jg_path, sva_module, rtl_src_path, i)

        print('$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$\n')
        with open(prop_file, 'r') as file:
            contents = file.read()
            print(contents)
        print('$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$\n')

        replace_assertions(prop_file, sva_module)
        run_JasperGold(sva_obj, jg_path)
        processed_svas.append(sva_obj)

    if processed_svas:
        for sva_obj in processed_svas:
            print(
                f"✅ Module `{sva_obj.module}` Summary — "
                f"Passed: {sva_obj.pass_count}, "
                f"Failed: {sva_obj.fail_count}, "
                f"Proven: {sva_obj.proven_count}, "
                f"CEX: {sva_obj.cex_count}"
            )
    else:
        print("⚠️ No valid SVA blocks were generated or processed.")
