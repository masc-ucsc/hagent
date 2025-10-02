#!/usr/bin/env python3
# Quick test to debug LLM configuration

import os
import sys
from pathlib import Path

from hagent.core.llm_wrap import LLM_wrap

# Add the hagent directory to sys.path for imports
current_dir = Path(__file__).parent
while current_dir.name != 'hagent' and current_dir.parent != current_dir:
    current_dir = current_dir.parent
sys.path.insert(0, str(current_dir.parent))


def test_llm_basic():
    """Test basic LLM functionality"""
    print('🔍 Testing LLM configuration...')

    try:
        # Initialize LLM with the corrected fallback config (like the fix)
        conf_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'v2chisel_batch_conf.yaml')
        print(f'📁 Using config file: {conf_file}')

        # Load template config to get default LLM settings
        from hagent.core.llm_template import LLM_template

        template_config = LLM_template(conf_file)

        # Get LLM configuration from template config
        llm_config = template_config.template_dict.get('v2chisel_batch', {}).get('llm', {})
        print(f'📊 LLM config extracted: {llm_config}')

        lw = LLM_wrap(
            name='test_debug',
            log_file='test_debug.log',
            conf_file=conf_file,
            overwrite_conf={'llm': llm_config},
        )
        print('✅ LLM initialized successfully')

        # Test with template config that includes prompts
        test_data = {
            'verilog_diff': "--- a/test.sv\n+++ b/test.sv\n@@ -1,1 +1,1 @@\n-wire test = 1'b0;\n+wire test = 1'b1;",
            'chisel_hints': 'val test = false.B',
        }

        print('🤖 Making test LLM call with prompt from template...')

        # Use template config that has the prompts properly structured
        response_list = template_config.inference(test_data, prompt_index='prompt_initial', n=1, llm_override={'llm': llm_config})

        print(f'📊 Response received: {type(response_list)}')
        print(f'📊 Response length: {len(response_list) if response_list else "None"}')

        if lw.last_error:
            print(f'❌ LLM error: {lw.last_error}')
            return False

        if not response_list or len(response_list) == 0:
            print('❌ LLM returned empty response')
            return False

        print(f'✅ LLM response: {response_list[0][:100]}...')
        return True

    except Exception as e:
        print(f'❌ Exception during LLM test: {e}')
        return False


if __name__ == '__main__':
    success = test_llm_basic()
    print(f'\n🎯 Test result: {"PASS" if success else "FAIL"}')
