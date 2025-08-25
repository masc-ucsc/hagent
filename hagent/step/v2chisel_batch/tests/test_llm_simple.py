#!/usr/bin/env python3
"""Simple LLM test to debug v2chisel_batch LLM issues"""

import os
import sys
from pathlib import Path

# Add project root to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent))

from hagent.core.llm_wrap import LLM_wrap


def test_llm_simple():
    """Test LLM with simple configuration"""

    # Use the v2chisel_batch config file
    conf_file = os.path.join(os.path.dirname(__file__), '..', 'v2chisel_batch_conf.yaml')

    print(f'Using config file: {conf_file}')
    print(f'Config file exists: {os.path.exists(conf_file)}')

    # Create LLM_wrap
    lw = LLM_wrap(name='v2chisel_batch', log_file='test_llm_simple.log', conf_file=conf_file)

    if lw.last_error:
        print(f'LLM_wrap error: {lw.last_error}')
        return False

    print('LLM_wrap created successfully')
    print(f'Config keys: {list(lw.config.keys())}')

    # Test simple inference
    template_data = {
        'verilog_diff': '--- a/test.sv\n+++ b/test.sv\n@@ -1,1 +1,1 @@\n-assign a = b;\n+assign a = ~b;',
        'chisel_hints': '// Simple test hint\nio.a := io.b',
    }

    try:
        response_list = lw.inference(template_data, prompt_index='prompt_initial', n=1)
        if response_list and len(response_list) > 0:
            print(f'✅ LLM response received: {len(response_list[0])} characters')
            print(f'Response preview: {response_list[0][:100]}...')
            return True
        else:
            print('❌ LLM returned empty response')
            return False
    except Exception as e:
        print(f'❌ LLM call failed: {e}')
        return False


if __name__ == '__main__':
    success = test_llm_simple()
    exit(0 if success else 1)
