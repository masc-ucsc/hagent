"""
Multi-strategy hint generation system for Chisel bug fixing.

This package provides a modular hint generation framework that combines
multiple strategies (ModuleFinder, SourceLocator, FuzzyGrep) to identify
relevant Chisel modules for bug repair.
"""

from .models import (
    ModuleSpan,
    ModuleHint,
    ModuleCandidate,
    TrialRecord,
    DiffInfo,
)

__all__ = [
    'ModuleSpan',
    'ModuleHint',
    'ModuleCandidate',
    'TrialRecord',
    'DiffInfo',
]
