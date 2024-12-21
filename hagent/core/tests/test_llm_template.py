# See LICENSE for details

import os
import yaml
from hagent.core.llm_template import LLM_template


def test_llm_template_good():
    good_template = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'llm_template_good_inp.yaml')

    temp = LLM_template(good_template)
    d = temp.format({'xx': 'potato'})

    dir = os.path.dirname(os.path.abspath(__file__))
    out_file = os.path.join(dir, 'llm_template_good_out.yaml')
    with open(out_file, 'r') as f:
        good_out = yaml.safe_load(f)

    # print(f"d       :{d}")
    # print(f"good_out:{good_out}")
    assert d == good_out


if __name__ == '__main__':  # pragma: no cover
    test_llm_template_good()
