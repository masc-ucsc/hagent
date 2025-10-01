"""
ModuleFinder strategy: Fuzzy name matching between Verilog and Chisel modules.

This strategy wraps the existing Module_finder tool to identify Chisel modules
by fuzzy-matching their names against Verilog module names extracted from the diff.
"""

from typing import List
from .strategy_base import HintStrategy
from .models import DiffInfo, ModuleHint
from .span_index import SpanIndex


class ModuleFinder(HintStrategy):
    """
    Strategy that uses fuzzy name matching to find candidate modules.

    Workflow:
    1. Extract Verilog module names from the diff
    2. Get all Scala/Chisel modules from span_index
    3. Compute fuzzy match confidence for each module
    4. Return modules with confidence > threshold
    """

    def __init__(self, min_confidence: float = 0.3):
        """
        Initialize ModuleFinder strategy.

        Args:
            min_confidence: Minimum confidence threshold (default 0.3)
        """
        self.min_confidence = min_confidence

    @property
    def name(self) -> str:
        """Strategy identifier."""
        return 'module_finder'

    def generate_hints(self, diff_info: DiffInfo, span_index: SpanIndex, builder=None) -> List[ModuleHint]:
        """
        Generate hints by fuzzy-matching module names.

        Args:
            diff_info: Information about the bug/diff
            span_index: Pre-built index of module spans
            builder: Unused (kept for interface consistency)

        Returns:
            List of ModuleHint objects sorted by confidence (descending)
        """
        hints = []

        # Get Verilog module name from diff_info
        verilog_module = diff_info.verilog_module
        if not verilog_module:
            return hints

        # Get all Chisel modules from span_index
        all_modules = span_index.get_all_modules()
        if not all_modules:
            return hints

        # Compute confidence for each module
        for module_span in all_modules:
            confidence = self._calculate_match_confidence(verilog_module, module_span.name)

            if confidence >= self.min_confidence:
                hint = ModuleHint(
                    module_id=module_span.module_id,
                    span=module_span,
                    confidence=confidence,
                    source=self.name,
                    evidence={
                        'verilog_module': verilog_module,
                        'chisel_module': module_span.name,
                        'fuzzy_ratio': confidence,
                        'match_type': self._classify_match(verilog_module, module_span.name, confidence),
                    },
                )
                hints.append(hint)

        # Sort by confidence (descending)
        hints.sort(key=lambda h: h.confidence, reverse=True)

        return hints

    def _calculate_match_confidence(self, verilog_name: str, chisel_name: str) -> float:
        """
        Calculate confidence score for a module name match.

        Uses the same logic as the existing Module_finder tool.

        Args:
            verilog_name: Verilog module name
            chisel_name: Chisel class/object name

        Returns:
            Confidence score in [0.0, 1.0]
        """
        if not verilog_name or not chisel_name:
            return 0.0

        # Exact match (case insensitive)
        if verilog_name.lower() == chisel_name.lower():
            return 1.0

        # Normalize names for comparison
        v_norm = self._normalize_name(verilog_name)
        c_norm = self._normalize_name(chisel_name)

        if v_norm == c_norm:
            return 0.9

        # Check containment
        confidence = 0.0
        if v_norm in c_norm or c_norm in v_norm:
            confidence = max(confidence, 0.8)

        # Check prefix/suffix
        if v_norm.endswith(c_norm) or c_norm.endswith(v_norm):
            confidence = max(confidence, 0.7)
        if v_norm.startswith(c_norm) or c_norm.startswith(v_norm):
            confidence = max(confidence, 0.7)

        # String similarity
        similarity = self._string_similarity(v_norm, c_norm)
        if similarity > 0.6:
            confidence = max(confidence, similarity * 0.6)

        return confidence

    def _normalize_name(self, name: str) -> str:
        """
        Normalize module name for comparison.

        Converts to lowercase, removes underscores, and strips common prefixes/suffixes.

        Args:
            name: Module name

        Returns:
            Normalized name
        """
        normalized = name.lower().replace('_', '')
        original = normalized

        # Remove common HDL prefixes/suffixes
        prefixes = ['top', 'module']
        suffixes = ['module', 'unit', 'top']

        for prefix in prefixes:
            if normalized.startswith(prefix) and len(normalized) > len(prefix):
                normalized = normalized[len(prefix) :]

        for suffix in suffixes:
            if normalized.endswith(suffix) and len(normalized) > len(suffix):
                normalized = normalized[: -len(suffix)]

        # Return normalized or original if normalization resulted in empty string
        return normalized if normalized else original

    def _string_similarity(self, s1: str, s2: str) -> float:
        """
        Calculate string similarity using character-based comparison.

        Args:
            s1: First string
            s2: Second string

        Returns:
            Similarity score in [0.0, 1.0]
        """
        if not s1 and not s2:
            return 1.0
        if not s1 or not s2:
            return 0.0
        if s1 == s2:
            return 1.0

        # Character-by-character matching
        max_len = max(len(s1), len(s2))
        min_len = min(len(s1), len(s2))

        matches = 0
        for i in range(min_len):
            if s1[i] == s2[i]:
                matches += 1

        return matches / max_len

    def _classify_match(self, verilog_name: str, chisel_name: str, confidence: float) -> str:
        """
        Classify the type of match for debugging.

        Args:
            verilog_name: Verilog module name
            chisel_name: Chisel module name
            confidence: Match confidence

        Returns:
            Match type string
        """
        if verilog_name.lower() == chisel_name.lower():
            return 'exact'
        elif confidence >= 0.9:
            return 'normalized_exact'
        elif confidence >= 0.8:
            return 'containment'
        elif confidence >= 0.7:
            return 'prefix_suffix'
        elif confidence >= 0.5:
            return 'similarity_high'
        else:
            return 'similarity_low'
