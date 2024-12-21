import yaml
import os
import time
import datetime
import litellm
from typing import List, Dict

from hagent.core.llm_template import llm_template

class llm_wrap:
    def __init__(self, name: str, conf_file: str, log_file: str, init_template: llm_template, chat_template: llm_template):
        self.name = name
        self.conf_file = conf_file
        self.log_file = log_file
        self.init_template = init_template
        self.chat_template = chat_template

        self.last_error = ''
        self.chat_history = []  # Stores messages as [{"role": "...", "content": "..."}]
        self.total_cost = 0.0
        self.total_tokens = 0
        self.total_time_ms = 0.0

        # Initialize litellm cache
        litellm.cache = litellm.Cache(type='disk')

        # Load configuration if possible
        self.llm_args = {}
        try:
            if os.path.exists(self.conf_file):
                with open(self.conf_file, 'r', encoding='utf-8') as f:
                    conf_data = yaml.safe_load(f)
                    if conf_data and self.name in conf_data and 'llm_wrap' in conf_data[self.name]:
                        self.llm_args = conf_data[self.name]['llm_wrap']
        except Exception as e:
            self._set_error(f'Error reading conf_file: {e}')

        # Try to open/create log file
        try:
            with open(self.log_file, 'a', encoding='utf-8'):
                pass
        except Exception as e:
            self._set_error(f'Error creating/opening log file: {e}')

    def _set_error(self, msg: str):
        self.last_error = msg

    def clear_history(self):
        self.chat_history.clear()
        data = {}
        data.update({'clear_history': True})
        if self.last_error:
            data['error'] = self.last_error
        self._log_event(event_type=f'{self.name}:llm_wrap.clear_history', data=data)

    def _log_event(self, event_type: str, data: Dict):
        entry = {
            'timestamp': datetime.datetime.utcnow().isoformat(),  # include microseconds
            'type': event_type,
        }
        entry.update(data)
        try:
            with open(self.log_file, 'a', encoding='utf-8') as lf:
                yaml.safe_dump([entry], lf, allow_unicode=True)
        except Exception as e:
            self._set_error(f'Logging error: {e}')

    def _call_llm(self, prompt_dict: Dict, is_chat: bool, n: int = 1) -> List[str]:
        self.last_error = ''
        start_time = time.time()

        # Decide template
        if is_chat:
            template = self.init_template if len(self.chat_history) == 0 else self.chat_template
        else:
            template = self.init_template

        # Format prompt
        try:
            formatted = template.format(prompt_dict)
            assert isinstance(formatted, dict)
        except Exception as e:
            self._set_error(f'Template formatting error: {e}')
            data = {'error': self.last_error}
            self._log_event(event_type=f'{self.name}:llm_wrap.error', data=data)
            return []

        # Check if template returned error
        if 'error' in formatted:
            self._set_error(f"Template returned error: {formatted['error']}")
            data = {'error': self.last_error}
            self._log_event(event_type=f'{self.name}:llm_wrap.error', data=data)
            return []

        # Construct messages
        # Start with chat_history
        messages = list(self.chat_history)

        # If template provides messages, use them; else use prompt as user message
        if 'messages' in formatted and isinstance(formatted['messages'], list):
            messages += formatted['messages']
        else:
            # If no messages, check for prompt
            prompt_text = formatted.get('prompt', '')
            if prompt_text:
                messages.append({'role': 'user', 'content': prompt_text})

        # For inference, messages might just be what we got. For chat, this is final messages to send.
        llm_call_args = {}
        llm_call_args.update(self.llm_args)
        llm_call_args['messages'] = messages
        if 'model' not in llm_call_args:
            llm_call_args['model'] = 'gpt-3.5-turbo'  # fallback

        # If inference, handle n
        if not is_chat and n > 1:
            llm_call_args['n'] = n

        # Call litellm
        try:
            r = litellm.completion(**llm_call_args)
        except Exception as e:
            self._set_error(f'litellm call error: {e}')
            data = {'error': self.last_error}
            self._log_event(event_type=f'{self.name}:llm_wrap.error', data=data)
            return []

        answers = []
        try:
            if 'choices' in r and isinstance(r['choices'], list):
                for c in r['choices']:
                    # "completion" style might use messages or text.
                    # According to snippet, messages likely in 'message'
                    if 'message' in c and 'content' in c['message']:
                        answers.append(c['message']['content'])
                    elif 'text' in c:
                        answers.append(c['text'])
            cost = r.get('cost', 0.0)
            tokens = r.get('tokens', 0)
        except Exception as e:
            cost = 0.0
            tokens = 0
            self._set_error(f'Parsing litellm response error: {e}')

        time_ms = (time.time() - start_time) * 1000.0
        self.total_cost += cost
        self.total_tokens += tokens
        self.total_time_ms += time_ms

        event_type = f'{self.name}:llm_wrap.chat' if is_chat else f'{self.name}:llm_wrap.inference'
        data = {'model': llm_call_args.get('model', ''), 'answers': answers, 'cost': cost, 'tokens': tokens, 'time_ms': time_ms}
        # Include the final prompt in data if we had one from template
        if 'prompt' in formatted:
            data['prompt'] = formatted['prompt']

        if self.last_error:
            data['error'] = self.last_error

        self._log_event(event_type=event_type, data=data)
        return answers

    def chat(self, prompt_dict: Dict) -> str:
        answers = self._call_llm(prompt_dict, is_chat=True, n=1)
        if len(answers) > 0:
            # Add assistant answer to chat history
            self.chat_history.append({'role': 'assistant', 'content': answers[0]})
            return answers[0]
        return ''

    def inference(self, prompt_dict: Dict, n: int = 1) -> List[str]:
        answers = self._call_llm(prompt_dict, is_chat=False, n=n)
        return answers
