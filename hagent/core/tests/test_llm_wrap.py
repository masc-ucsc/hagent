#!/usr/bin/env python3
# See LICENSE for details

import os
from unittest.mock import patch, MagicMock
from hagent.core.llm_wrap import LLM_wrap
from hagent.core.llm_template import LLM_template


def test_llm_wrap_caching():
    templ_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'llm_wrap_caching.yaml')
    conf_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'llm_wrap_conf1.yaml')

    templ = LLM_template(templ_file)

    lw = LLM_wrap()
    lw.from_file(
        name='test_caching', log_file='test_llm_wrap_caching.log', conf_file=conf_file, init_template=templ, chat_template=templ
    )

    jokes1 = lw.inference({}, n=1)
    jokes2 = lw.inference({}, n=1)

    # Since caching is enabled, both jokes should match
    assert len(jokes1) == 1
    assert len(jokes2) == 1
    assert jokes1[0].endswith(jokes2[0]), f"{jokes1} vs {jokes2}"


def test_llm_wrap_n_bad_conf():
    conf_file = 'nonexistent.yaml'
    templ = MagicMock(spec=LLM_template)
    templ.format.return_value = [{'role': 'user', 'content': 'mocked prompt'}]

    lw = LLM_wrap()
    lw.from_file(
        name='test_n',
        log_file='mocked_log_file.log',
        conf_file=conf_file,
        init_template=templ,
        chat_template=templ,
    )

    with patch(
        'litellm.completion',
        return_value={
            'choices': [{'message': {'content': 'response'}}] * 5,
            'cost': 0.1,
            'tokens': 50,
        },
    ):
        res = lw.inference({}, n=5)
        assert len(res) == 0


def test_llm_wrap_n_diff():
    conf_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'llm_wrap_conf1.yaml')

    templ = LLM_template(
        [
            {'role': 'system', 'content': 'just provide a numeric answer'},
            {'role': 'user', 'content': 'Give me a random number between 1 and 3000000'},
        ]
    )

    lw = LLM_wrap()
    lw.from_file(
        name='test_caching', log_file='test_llm_wrap_caching.log', conf_file=conf_file, init_template=templ, chat_template=templ
    )

    res = lw.inference({}, n=3)
    assert len(res) == 3

    assert res[0] != res[1]
    assert res[0] != res[2]


def test_llm_wrap_empty_config():
    lw = LLM_wrap()
    lw.from_file(
        name='test_empty_config',
        log_file='test_empty_config.log',
        conf_file='nonexistent.yaml',
        init_template=MagicMock(spec=LLM_template),
        chat_template=MagicMock(spec=LLM_template),
    )

    assert lw.llm_args == {}
    assert 'conf_file:nonexistent.yaml must specify llm "model"' in lw.last_error


def test_llm_wrap_template_format_error():
    mock_template = MagicMock(spec=LLM_template)
    mock_template.format.side_effect = Exception('Formatting error')

    lw = LLM_wrap()
    lw.from_file(
        name='test_template_format_error',
        log_file='test_template_format_error.log',
        conf_file='nonexistent.yaml',
        init_template=mock_template,
        chat_template=mock_template,
    )

    result = lw.inference({}, n=1)
    assert result == [], 'Expected empty result when template formatting fails'
    assert 'template formatting error' in lw.last_error


if __name__ == '__main__':  # pragma: no cover
    test_llm_wrap_caching()
    test_llm_wrap_n_bad_conf()
    test_llm_wrap_n_diff()
    test_llm_wrap_empty_config()
    test_llm_wrap_template_format_error()
