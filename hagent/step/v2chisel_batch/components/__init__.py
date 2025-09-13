"""
Components package for V2chisel_batch refactoring.

This package contains individual classes extracted from the monolithic
v2chisel_batch.py to improve maintainability and testability.

Components:
- BugInfo: Handles bug information extraction and parsing
- HintsGenerator: Manages Chisel code hints generation for bug fixing
- GoldenDesignBuilder: Creates golden design files for LEC verification
"""

from .bug_info import BugInfo
from .hints_generator import HintsGenerator
from .golden_design_builder import GoldenDesignBuilder

__all__ = ['BugInfo', 'HintsGenerator', 'GoldenDesignBuilder']
