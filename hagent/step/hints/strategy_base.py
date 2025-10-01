"""
Abstract base class for hint generation strategies.

All hint strategies must implement the HintStrategy interface, which takes
a DiffInfo and SpanIndex, and returns a list of ModuleHint objects.
"""

from abc import ABC, abstractmethod
from typing import List
from .models import DiffInfo, ModuleHint
from .span_index import SpanIndex


class HintStrategy(ABC):
    """
    Abstract base for hint generation strategies.

    Each strategy analyzes a Verilog diff and proposes candidate Chisel modules
    that may need modification to fix the bug.
    """

    @abstractmethod
    def generate_hints(self, diff_info: DiffInfo, span_index: SpanIndex, builder=None) -> List[ModuleHint]:
        """
        Generate module hints for the given diff.

        Args:
            diff_info: Information about the bug/diff
            span_index: Pre-built index of module spans
            builder: Builder instance for file I/O (handles Docker/local)

        Returns:
            List of ModuleHint objects (may be empty)
        """
        pass

    @property
    @abstractmethod
    def name(self) -> str:
        """
        Strategy identifier.

        Returns:
            One of: 'module_finder', 'source_locator', 'fuzzy_grep'
        """
        pass

    def __repr__(self) -> str:
        """String representation of strategy."""
        return f"{self.__class__.__name__}(name='{self.name}')"
