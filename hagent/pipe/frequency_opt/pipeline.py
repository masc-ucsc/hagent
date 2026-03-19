# See LICENSE for details
"""
Frequency optimization pipeline definition.

This module defines the pipeline structure:
1. SynthSTA: Initial RTL synthesis and baseline timing analysis
2. Extract Critical: Find modules on critical path
3. Optimization Loop:
   - LLM Optimize (with internal LEC retry)
   - Evaluate (re-synth, re-STA, compare)
   - Loop until target met or max iterations

Pipeline structure:

    synth_sta ->  extract_critical -> [optimization_loop] -> (end)
                                               |
                              +----------------+----------------+
                              |                                 |
                              v                                 |
                        llm_optimize -----> evaluate -----------+
                              ^                 |
                              |                 v
                              +---- (if should_continue) ----+

Environment variables:
    The pipeline reads 'env_vars' from the config YAML and exports them
    to os.environ before running any steps. This ensures all steps and
    subprocesses have access to required environment variables.
"""

import os
from pathlib import Path
from typing import Dict

from hagent.pipe.frequency_opt.steps import (
    SynthSTAStep,
    ExtractCriticalStep,
    LLMOptimizeWithLECStep,
    EvaluateStep,
)


def setup_environment(data: Dict) -> None:
    """
    Set environment variables from config before running pipeline.

    Reads 'env_vars' dict from top-level YAML config and exports
    each key-value pair to os.environ.

    Args:
        data: Pipeline config data loaded from YAML
    """
    env_vars = data.get('env_vars', {})
    if env_vars:
        for key, value in env_vars.items():
            os.environ[key] = str(value)
        print(f'Exported env vars: {", ".join(env_vars.keys())}')

