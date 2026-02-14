# See LICENSE for details
"""
Frequency Optimization Pipeline.

This pipeline optimizes RTL designs for timing/frequency by:
1. Synthesizing and analyzing baseline timing
2. Extracting critical path modules
3. Using LLM to generate optimized variants
4. Verifying equivalence (LEC)
5. Re-synthesizing and evaluating improvement

Usage:
    uv run python -m hagent.pipe.frequency_opt.run config.yaml
"""

from hagent.pipe.frequency_opt.orchestrator import PipelineOrchestrator
from hagent.pipe.frequency_opt.pipeline import create_frequency_opt_pipeline

__all__ = ['PipelineOrchestrator', 'create_frequency_opt_pipeline']
