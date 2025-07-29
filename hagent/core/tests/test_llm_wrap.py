#!/usr/bin/env python3
# See LICENSE for details

import os
import tempfile
import pytest
from unittest.mock import patch

from hagent.core.llm_wrap import LLM_wrap


def test_llm_wrap_caching():
    # Use existing configuration file for caching test.
    conf_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'llm_wrap_conf1.yaml')

    lw = LLM_wrap(name='test_caching', log_file='test_llm_wrap_caching.log', conf_file=conf_file)

    jokes1 = lw.inference({}, 'use_prompt1', n=1)
    jokes2 = lw.inference({}, 'use_prompt1', n=1)

    # Since caching is enabled, both responses should match.
    assert len(jokes1) == 1
    assert len(jokes2) == 1
    assert jokes1[0].endswith(jokes2[0]), f'{jokes1} vs {jokes2}'


def test_llm_wrap_n_diff():
    conf_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'llm_wrap_conf1.yaml')

    lw = LLM_wrap(name='test_caching', log_file='test_llm_wrap_caching.log', conf_file=conf_file)

    res = lw.inference({}, 'use_prompt_random', n=3)
    assert len(res) == 3
    assert res[0] != res[1]
    assert res[0] != res[2]


def test_bad_config_file_nonexistent():
    # Test with a non-existent configuration file.
    non_existent_file = '/non/existent/conf.yaml'
    lw = LLM_wrap('test_bad_config', non_existent_file, 'test_bad_config.log')
    assert 'unable to read conf_file' in lw.last_error

    result = lw.inference({}, 'some_prompt', n=1)
    # Expect empty result and an error about missing llm "model".
    assert 'unable to read conf_file' in lw.last_error
    assert result == []

def test_bad_prompt():
    # Test with a non-existent configuration file.
    conf_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'llm_wrap_conf1.yaml')

    lw = LLM_wrap(name='test_caching', log_file='test_llm_wrap_caching.log', conf_file=conf_file)

    result = lw.inference({}, 'some_bad_prompt', n=1)

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

        result = lw.inference({}, 'some_prompt', n=1)
        assert result == []
        assert 'specify llm section' in lw.last_error
    finally:
        os.unlink(tmp_path)


def test_missing_env_var(monkeypatch):

    # Remove the environment variable
    if "AWS_BEARER_TOKEN_BEDROCK" in os.environ:
        monkeypatch.delenv("AWS_BEARER_TOKEN_BEDROCK", raising=False)

        # Use existing configuration file for caching test.
        conf_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'llm_wrap_conf1.yaml')

        lw = LLM_wrap(name='test_caching', log_file='test_llm_wrap_caching.log', conf_file=conf_file)

        with pytest.raises(ValueError):
            jokes = lw.inference({}, 'use_prompt1', n=1)

        assert "Environment" in lw.last_error
    else:
        assert False, "Must set AWS_BEARER_TOKEN_BEDROCK for unit test"


if __name__ == '__main__':  # pragma: no cover
    test_llm_wrap_caching()
    test_llm_wrap_n_diff()
    test_bad_config_file_nonexistent()
    test_bad_config_file_bad_yaml()
    # test_missing_env_var()
    test_bad_prompt()

