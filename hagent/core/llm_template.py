# See LICENSE for details

from typing import List, Dict
import yaml
import os
# from jinja2 import Environment


class LLM_template:
    def validate_template(self, data):  # No type check, because it generates errors for incorrect types
        if not isinstance(data, list):
            return 'the data is not a list'

        if not data:
            return 'the list is empty.'

        allowed_roles = {'user', 'system', 'assistant'}

        for index, item in enumerate(data):
            if not isinstance(item, dict):
                return f'item at index {index} is not a dictionary.'

            # Check for 'role' and 'content' keys
            if 'role' not in item:
                return f"item at index {index} is missing the 'role' key."
            if 'content' not in item:
                return f"item at index {index} is missing the 'content' key."

            # Check if the 'role' is valid
            role = item['role']
            if role not in allowed_roles:
                return f"invalid role '{role}' at index {index}. Allowed roles are 'user', 'system', or 'assistant'."

        # Check if the last item's role is 'user'
        if data[-1]['role'] != 'user':
            return "the last item's role must be 'user'."

        return None

    def __init__(self, data):
        self.file_name = ''
        if isinstance(data, str):
            if not os.path.exists(data):
                dir = os.path.dirname(os.path.abspath(__file__))
                inp_file = os.path.join(dir, data)
                if os.path.exists(inp_file):
                    data = inp_file
            try:
                with open(data, 'r') as f:
                    self.template_dict = yaml.safe_load(f)
                self.file_name = data
            except FileNotFoundError:
                self.template_dict = {'error': f"LLM_template, file '{data}' does not exist"}
            except yaml.YAMLError as e:
                self.template_dict = {'error': f"LLM_template, file '{data}' did not parse correctly: {e}"}
        elif isinstance(data, list):
            self.template_dict = data # Should be a list of dicts, but checked in validate_template
        else:
            self.template_dict = {'error': 'LLM_template could not process {str}'}

        if 'error' not in self.template_dict:
            err = self.validate_template(self.template_dict)
            if err is not None:
                self.template_dict = {'error': f'LLM_template file {data} fails because {err}'}

        if 'error' in self.template_dict:
            print('ERROR:', self.template_dict.get('error'))

    def format(self, context: Dict) -> List[Dict]:
        if 'error' in self.template_dict:
            return self.template_dict

        result = []
        for item in self.template_dict:
            ctx = {}
            if isinstance(item, dict):
                for key, value in item.items():
                    if isinstance(value, str):
                        fmt = value
                        try:
                            fmt = value.format(**context)
                        except KeyError as e:
                            txt = f'LLM_template::format {self.file_name} has undefined variable {e}'
                            print(f'ERROR: {txt}')
                            return [{'error': txt}]
                        ctx[key] = fmt
                    else:
                        ctx[key] = value
                result.append(ctx)
            else:
                assert False, 'The template_dict should be validate before, so it should not fail now'

        return result
