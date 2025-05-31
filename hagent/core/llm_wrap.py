import os
import time
import datetime
import litellm
import sys
from typing import List, Dict

from ruamel.yaml import YAML
from ruamel.yaml.scalarstring import LiteralScalarString

from hagent.core.llm_template import LLM_template


def dict_deep_merge(dict1: Dict, dict2: Dict) -> Dict:
    """Recursively merges dict2 into dict1, overwriting only leaf values.

    Args:
        dict1: The base dictionary (will be modified).
        dict2: The dictionary to merge into dict1.

    Returns:
        dict1 (modified).
    """
    for key, value in dict2.items():
        if key in dict1:
            if isinstance(dict1[key], dict) and isinstance(value, dict):
                dict_deep_merge(dict1[key], value)  # Recursive call for nested dicts
            else:
                dict1[key] = value  # Overwrite at leaf level
        else:
            dict1[key] = value  # Add new key-value pair
    return dict1


class LLM_wrap:
    def load_config(self) -> Dict:
        if not os.path.exists(self.conf_file):
            self._set_error(f'unable to read conf_file: {self.conf_file}')
            return {}

        try:
            yaml_loader = YAML(typ='safe')
            with open(self.conf_file, 'r', encoding='utf-8') as f:
                conf_data = yaml_loader.load(f)

            if not conf_data:
                return {}

            # Case-insensitive search for self.name
            lower_name = self.name.lower()
            config_name = next((k for k in conf_data if k.lower() == lower_name), None)
            if not config_name:
                return {}

            return conf_data[config_name]

        except Exception as e:
            self._set_error(f'reading conf_file: {e}')
            return {}

        return {}

    def check_env_keys(self, model: str) -> bool:
        if model.startswith('fireworks'):
            required_key = 'FIREWORKS_AI_API_KEY'
        elif model.startswith('openai'):
            required_key = 'OPENAI_API_KEY'
        elif model.startswith('anthropic'):
            required_key = 'ANTHROPIC_API_KEY'
        elif model.startswith('replicate'):
            required_key = 'REPLICATE_API_KEY'
        elif model.startswith('cohere'):
            required_key = 'COHERE_API_KEY'
        elif model.startswith('together_ai'):
            required_key = 'TOGETHER_AI_API_KEY'
        elif model.startswith('openrouter'):
            required_key = 'OPENROUTER_API_KEY'
        elif model.startswith('ollama'):
            # Ollama access is achieved through a URL such as 'http://localhost:11434'
            required_key = 'OLLAMA_API_BASE'
        # Add more providers as needed...
        else:
            # No specific key required for this model type (or you can raise an error if unknown)
            print(f'ERROR: No environment variable check defined for model: {model}', file=sys.stderr)
            return False

        if os.environ.get(required_key) is None:
            error_message = f"Error: Environment variable '{required_key}' is not set for model '{model}'."
            print(error_message, file=sys.stderr)  # Print to stderr
            self._set_error(error_message)
            raise ValueError(error_message)

        return True

    def __init__(self, name: str, conf_file: str, log_file: str, overwrite_conf: Dict = {}):
        self.name = name
        self.conf_file = conf_file
        self.log_file = log_file

        self.last_error = ''
        self.chat_history = []  # Stores messages as [{"role": "...", "content": "..."}]
        self.responses = []  # Stores the complete litellm response for tracing LLM calls.
        self.total_cost = 0.0
        self.total_tokens = 0
        self.total_time_ms = 0.0

        # Initialize litellm cache
        litellm.cache = litellm.Cache(type='disk')

        self.config = {}

        if os.path.exists(self.conf_file):
            self.config = self.load_config()
        elif self.conf_file:
            self._set_error(f'unable to read conf_file {conf_file}')
            return

        if overwrite_conf:
            self.config = dict_deep_merge(self.config, overwrite_conf)

        if 'llm' not in self.config:
            self._set_error(f'conf_file:{conf_file} or overwrite_conf must specify llm section')
            return

        self.llm_args = self.config['llm']

        if 'model' not in self.llm_args:
            self._set_error(f'conf_file:{conf_file} must specify llm "model" in section {name}')
            return

        try:
            with open(self.log_file, 'a', encoding='utf-8'):
                pass
        except Exception as e:
            self._set_error(f'creating/opening log file: {e}')

    def _set_error(self, msg: str):
        self.last_error = msg
        print(msg, file=sys.stderr)

    def clear_history(self):
        self.chat_history.clear()
        data = {}
        data.update({'clear_history': True})
        if self.last_error:
            data['error'] = self.last_error
        self._log_event(event_type=f'{self.name}:LLM_wrap.clear_history', data=data)

    def _log_event(self, event_type: str, data: Dict):
        def process_multiline_strings(obj):
            """
            Recursively convert strings with newlines into LiteralScalarString so that they
            are output in literal block style.
            """
            if isinstance(obj, dict):
                return {k: process_multiline_strings(v) for k, v in obj.items()}
            elif isinstance(obj, list):
                return [process_multiline_strings(item) for item in obj]
            elif isinstance(obj, str) and '\n' in obj:
                # Wrap the multiline string so that ruamel.yaml outputs it using literal block style.
                return LiteralScalarString(obj)
            return obj

        def append_log(dt, file):
            # Process data to wrap multiline strings.
            processed_data = process_multiline_strings(dt)
            yaml = YAML()
            # Configure indentation (optional).
            yaml.indent(mapping=2, sequence=4, offset=2)
            yaml.dump(processed_data, file)

        entry = {
            'timestamp': datetime.datetime.now(datetime.UTC).isoformat(),  # include microseconds
            'type': event_type,
        }
        entry.update(data)
        try:
            with open(self.log_file, 'a', encoding='utf-8') as lf:
                append_log(entry, lf)
        except Exception as e:
            self._set_error(f'unable to log: {e}')

    def _call_llm(self, prompt_dict: Dict, prompt_index: str, n: int, max_history: int) -> List[str]:
        if self.last_error:
            return []

        start_time = time.time()

        template_dict = self.config.get(prompt_index, {})
        if not template_dict:
            if not self.conf_file:
                self._set_error(f'unable to find {prompt_index} entry in {self.config}')
            else:
                self._set_error(f'unable to find {prompt_index} entry in {self.conf_file}')
            return []

        template = LLM_template(template_dict)
        if template.last_error:
            self._set_error(f'template failed with {template.last_error}')
            return []

        # Format prompt
        try:
            formatted = template.format(prompt_dict)
            assert isinstance(formatted, list), 'Data should be a list'
        except Exception as e:
            self._set_error(f'template formatting error: {e}')
            data = {'error': self.last_error}
            self._log_event(event_type=f'{self.name}:LLM_wrap.error', data=data)
            return []

        # Check if template returned error
        if 'error' in formatted:
            self._set_error(f'template returned error: {formatted["error"]}')
            data = {'error': self.last_error}
            self._log_event(event_type=f'{self.name}:LLM_wrap.error', data=data)
            return []

        if max_history > 0:
            messages = self.chat_history[:max_history]
        else:
            messages = []
        messages += formatted

        # For inference, messages might just be what we got. For chat, this is final messages to send.
        llm_call_args = {}
        llm_call_args.update(self.llm_args)
        llm_call_args['messages'] = messages
        llm_call_args['n'] = n

        model = llm_call_args.get('model', '')
        if model == '':
            self._set_error('empty model name. No default model used')
            return []

        if not self.check_env_keys(model):
            self._set_error(f'environment keys not set for {model}')
            return []

        # Call litellm
        try:
            start = time.time()
            r = litellm.completion(**llm_call_args)

            end = time.time()
            # Augment the litellm.ModelResponse with duration.
            response = r.to_dict()
            # Overwrite the response 'created' time to get matching sub-second accuracy.
            response['created'] = start
            response['elapsed'] = end - start
        except Exception as e:
            self._set_error(f'litellm call error: {e}')
            data = {'error': self.last_error}
            self._log_event(event_type=f'{self.name}:LLM_wrap.error', data=data)
            return []

        answers = []
        cost = 0.0
        tokens = 0
        try:
            cost = litellm.completion_cost(completion_response=r)
        except Exception:
            cost = 0  # Model may not be updated for cost

        if cost == 0:
            # Simple proxy for https://fireworks.ai/pricing
            if 'deepseek-r1' in model:
                cost = 3.0 * tokens / 1e6
            else:
                cost = 0.9 * tokens / 1e6

        try:
            for c in r['choices']:
                answers.append(c['message']['content'])

            usage = r['usage']
            tokens += usage.get('total_tokens', 0)
        except Exception as e:
            self._set_error(f'parsing litellm response error: {e}')

        time_ms = (time.time() - start_time) * 1000.0
        self.total_cost += cost
        self.total_tokens += tokens
        self.total_time_ms += time_ms

        use_history = min(len(self.chat_history), max_history)
        event_type = f'{self.name}:LLM_wrap.inference with history={use_history}'

        data = {
            'model': model,
            'cost': cost,
            'tokens': tokens,
            'time_ms': time_ms,
            'prompt': formatted,
            'answers': answers,
        }

        if self.last_error:
            data['error'] = self.last_error

        self._log_event(event_type=event_type, data=data)

        response['cost'] = cost
        self.responses.append(response)
        return answers

    def inference(self, prompt_dict: Dict, prompt_index: str, n: int = 1, max_history: int = 0) -> List[str]:
        answers = self._call_llm(prompt_dict, prompt_index, n=n, max_history=max_history)
        return answers
