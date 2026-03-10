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

from hagent.pipe.frequency_opt.orchestrator import PipelineOrchestrator
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


def create_frequency_opt_pipeline(output_dir: Path, max_iterations: int = 5) -> PipelineOrchestrator:
    """
    Create the frequency optimization pipeline.

    Args:
        output_dir: Directory for pipeline outputs
        max_iterations: Maximum optimization loop iterations

    Returns:
        Configured PipelineOrchestrator ready to run

    Usage:
        data = load_yaml('config.yaml')
        setup_environment(data)  # Set env vars first
        pipeline = create_frequency_opt_pipeline(Path('./output'))
        return_code = pipeline.run(data)
    """
    pipeline = PipelineOrchestrator('frequency_opt', output_dir)

    # Phase 1: Baseline analysis
    pipeline.add_step('synth_sta', SynthSTAStep, next_node='extract_critical')
    pipeline.add_step('extract_critical', ExtractCriticalStep, next_node='optimization_loop')

    # Phase 2: Optimization loop
    # Body steps: LLM optimization (with internal LEC retry) -> Evaluate
    # Loop continues while 'should_continue' is True
    # pipeline.add_loop(
    #     name='optimization_loop',
    #     body_steps=['llm_optimize', 'evaluate'],
    #     condition_field='should_continue',
    #     max_iterations=max_iterations,
    #     on_exit=None,  # End of pipeline
    # )

    # # Steps used in the optimization loop
    # pipeline.add_step('llm_optimize', LLMOptimizeWithLECStep)
    # pipeline.add_step('evaluate', EvaluateStep)

    return pipeline
