# See LICENSE for details
"""
Steps for the frequency optimization pipeline.

Each step:
- Reads configuration from YAML (using schema.ConfigGroup classes)
- Reads outputs from previous steps (using schema.require_field)
- Writes outputs for subsequent steps (using schema.set_field)
- Handles its own filesystem validation when using files

Steps:
- SynthSTAStep: RTL synthesis followed by static timing analysis
- ExtractCriticalStep: Extract modules on critical path
- LLMOptimizeWithLECStep: LLM optimization with internal LEC retry
- EvaluateStep: Compare timing and decide whether to continue
"""

from hagent.pipe.frequency_opt.steps.synth_sta import SynthSTAStep
from hagent.pipe.frequency_opt.steps.extract_critical import ExtractCriticalStep
from hagent.pipe.frequency_opt.steps.llm_optimize import LLMOptimizeWithLECStep
from hagent.pipe.frequency_opt.steps.evaluate import EvaluateStep

__all__ = [
    'SynthSTAStep',
    'ExtractCriticalStep',
    'LLMOptimizeWithLECStep',
    'EvaluateStep',
]
