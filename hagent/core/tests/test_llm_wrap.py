#!/usr/bin/env python3
# See LICENSE for details

import os
import tempfile

from hagent.core.llm_wrap import LLM_wrap


def test_llm_wrap_caching():
    # Use existing configuration file for caching test.
    conf_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'llm_wrap_conf1.yaml')

    lw = LLM_wrap(name='test_caching', log_file='test_llm_wrap_caching.log', conf_file=conf_file)

    jokes1 = lw._inference({}, 'use_prompt1', n=1)
    jokes2 = lw._inference({}, 'use_prompt1', n=1)

    # Since caching is enabled, both responses should match.
    assert len(jokes1) == 1
    assert len(jokes2) == 1
    assert jokes1[0].endswith(jokes2[0]), f'{jokes1} vs {jokes2}'


def test_llm_wrap_n_diff():
    import litellm

    conf_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'llm_wrap_conf1.yaml')

    lw = LLM_wrap(name='test_caching', log_file='test_llm_wrap_caching.log', conf_file=conf_file)

    # disable cache
    cache = litellm.cache
    litellm.cache = None

    res = lw._inference({}, 'use_prompt_random', n=3)
    assert len(res) == 3
    print(res)
    assert res[0] != res[1]
    assert res[0] != res[2]

    litellm.cache = cache


def test_bad_config_file_nonexistent():
    # Test with a non-existent configuration file.
    non_existent_file = '/non/existent/conf.yaml'
    lw = LLM_wrap('test_bad_config', non_existent_file, 'test_bad_config.log')
    assert 'unable to read conf_file' in lw.last_error

    result = lw._inference({}, 'some_prompt', n=1)
    # Expect empty result and an error about missing llm "model".
    assert 'unable to read conf_file' in lw.last_error
    assert result == []


def test_bad_prompt():
    # Test with a non-existent configuration file.
    conf_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'llm_wrap_conf1.yaml')

    lw = LLM_wrap(name='test_caching', log_file='test_llm_wrap_caching.log', conf_file=conf_file)

    result = lw._inference({}, 'some_bad_prompt', n=1)

    assert 'unable to find' in lw.last_error
    assert result == []


def test_bad_config_file_bad_yaml():
    # Create a temporary file with invalid YAML content.
    with tempfile.NamedTemporaryFile(mode='w', delete=False) as tmp:
        tmp.write('invalid: [yaml, : :')
        tmp_path = tmp.name
    try:
        lw = LLM_wrap('test_bad_yaml', tmp_path, 'test_bad_yaml.log')
        assert 'specify llm section' in lw.last_error

        result = lw._inference({}, 'some_prompt', n=1)
        assert result == []
        assert 'specify llm section' in lw.last_error
    finally:
        os.unlink(tmp_path)


def test_missing_env_var(monkeypatch):
    # Test environment variable validation by removing all common LLM provider keys
    env_vars_to_remove = [
        'AWS_ACCESS_KEY_ID',
        'AWS_SECRET_ACCESS_KEY',
        'AWS_BEARER_TOKEN_BEDROCK',
        'OPENAI_API_KEY',
        'ANTHROPIC_API_KEY',
        'FIREWORKS_AI_API_KEY',
        'OPENROUTER_API_KEY',
        'REPLICATE_API_KEY',
        'COHERE_API_KEY',
        'TOGETHER_AI_API_KEY',
        'OLLAMA_API_BASE',
    ]

    # Remove all LLM provider environment variables
    for var in env_vars_to_remove:
        monkeypatch.delenv(var, raising=False)

    # Use existing configuration file for caching test.
    conf_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'llm_wrap_conf1.yaml')

    lw = LLM_wrap(name='test_caching', log_file='test_llm_wrap_caching.log', conf_file=conf_file)

    # Should return empty result since check_env_keys returns False
    result = lw._inference({}, 'use_prompt1', n=1)
    assert result == []
    assert 'environment' in lw.last_error.lower()


def test_hagent_llm_model_override(monkeypatch):
    # Test that HAGENT_LLM_MODEL environment variable overrides the config file model
    conf_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'llm_wrap_conf1.yaml')

    # Set the environment variable to a fake provider/model
    fake_model = 'fakeprovider/fake-model'
    monkeypatch.setenv('HAGENT_LLM_MODEL', fake_model)

    lw = LLM_wrap(name='test_caching', log_file='test_llm_model_override.log', conf_file=conf_file)

    # Verify the model was overridden
    assert lw.llm_args['model'] == fake_model

    # Try to make an inference call - should fail with unsupported model error
    result = lw._inference({}, 'use_prompt1', n=1)
    assert result == []
    assert 'environment keys not set for fakeprovider/fake-model' in lw.last_error


def test_openai_model():
    import pytest

    # Skip test if OPENAI_API_KEY is not set
    if not os.environ.get('OPENAI_API_KEY'):
        pytest.skip('OPENAI_API_KEY not set')

    # Simple LLM configuration for OpenAI
    llm_config = {'model': 'openai/gpt-4o-mini', 'max_tokens': 100, 'temperature': 0.7}

    # Use a simple prompt for testing
    prompt_config = {
        'test_prompt': [
            {
                'role': 'system',
                'content': 'You are a helpful assistant. Respond briefly.',
            },
            {
                'role': 'user',
                'content': 'Say hello in exactly 3 words.',
            },
        ]
    }

    # Complete configuration
    complete_config = {'llm': llm_config, **prompt_config}

    lw = LLM_wrap(
        name='test_openai',
        log_file='test_openai.log',
        conf_file='',
        overwrite_conf=complete_config,
    )

    assert not lw.last_error, f'LLM initialization error: {lw.last_error}'

    # Make test LLM call
    response_list = lw.inference({}, prompt_index='test_prompt', n=1)

    assert not lw.last_error, f'LLM error: {lw.last_error}'
    assert response_list and len(response_list) > 0, 'LLM returned empty response'
    assert len(response_list[0]) > 0, 'Response text is empty'


if __name__ == '__main__':  # pragma: no cover
    test_llm_wrap_caching()
    test_llm_wrap_n_diff()
    test_bad_config_file_nonexistent()
    test_bad_config_file_bad_yaml()
    # test_missing_env_var()
    # test_hagent_llm_model_override()
    test_bad_prompt()
    test_openai_model()
