#!/usr/bin/env python3
# Test OpenAI O3 specifically

import sys
from pathlib import Path

from hagent.core.llm_wrap import LLM_wrap

# Add the hagent directory to sys.path for imports
current_dir = Path(__file__).parent
while current_dir.name != 'hagent' and current_dir.parent != current_dir:
    current_dir = current_dir.parent
sys.path.insert(0, str(current_dir.parent))


def test_openai_o3():
    """Test OpenAI O3 specifically to debug API issue"""
    print('🔍 Testing OpenAI O3 API directly...')

    try:
        # Simple LLM configuration for O3
        llm_config = {'model': 'openai/o3-mini-2025-01-31', 'max_tokens': 1000, 'temperature': 1}

        # Use the exact same prompt structure as v2chisel_batch
        prompt_config = {
            'prompt_initial': [
                {
                    'role': 'system',
                    'content': 'You are an expert AI assistant specialized in translating Verilog changes to corresponding Chisel code modifications.\nYour goal is to generate precise Chisel diffs that, when applied, will produce Verilog logically equivalent to the target changes.',
                },
                {
                    'role': 'user',
                    'content': 'I have a Chisel hardware design that generates Verilog. I need to modify the Chisel code to match specific changes made to the Verilog.\n\nHere is the unified diff showing the desired Verilog changes:\n```\n{verilog_diff}\n```\n\nHere are hints from the corresponding Chisel code that likely need modification:\n```\n{chisel_hints}\n```\n\nPlease generate a unified diff for the Chisel code that will produce the desired Verilog changes.\n\nRequirements:\n- Output ONLY the unified diff in standard format\n- Use minimal hunks containing only the necessary changes\n- Do NOT include any explanation, commentary, or notes\n- Ensure the diff can be applied to existing Chisel source files\n\nGenerate the Chisel unified diff now:',
                },
            ]
        }

        # Complete configuration
        complete_config = {'llm': llm_config, **prompt_config}

        print(f'📊 Complete config: {complete_config}')

        lw = LLM_wrap(
            name='test_openai',
            log_file='test_openai.log',
            conf_file='',  # No file
            overwrite_conf=complete_config,
        )

        if lw.last_error:
            print(f'❌ LLM initialization error: {lw.last_error}')
            return False

        print('✅ LLM initialized successfully')

        # Test with the same data structure as v2chisel_batch
        test_data = {
            'verilog_diff': "--- a/Control.sv\n+++ b/Control.sv\n@@ -27,1 +27,1 @@\n-      ? (io_funct3 == 3'h0 & io_inputx == io_inputy | io_funct3 == 3'h1\n+      ? (io_funct3 == 3'h0 & io_inputx == io_inputy | io_funct3 == 3'h3",
            'chisel_hints': 'class Control extends Module {\n  val signals = Control.Signals(...)\n  // Branch control logic\n}',
        }

        print('🤖 Making test LLM call with v2chisel_batch data...')
        response_list = lw.inference(test_data, prompt_index='prompt_initial', n=1)

        print(f'📊 Response received: {type(response_list)}')
        print(f'📊 Response length: {len(response_list) if response_list else "None"}')

        if lw.last_error:
            print(f'❌ LLM error: {lw.last_error}')
            return False

        if not response_list or len(response_list) == 0:
            print('❌ LLM returned empty response')
            return False

        print(f'✅ LLM response: {response_list[0]}')
        return True

    except Exception as e:
        print(f'❌ Exception during LLM test: {e}')
        return False


if __name__ == '__main__':
    success = test_openai_o3()
    print(f'\n🎯 Test result: {"PASS" if success else "FAIL"}')
