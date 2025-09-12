#!/usr/bin/env python3
"""
BugInfo class for extracting and managing bug-specific information.

This class encapsulates the logic for extracting bug information from
the bug_entry dictionary, including file name, module name, and verilog diff.
"""

import os
from typing import Dict, Any


class BugInfo:
    """
    Extracts and manages bug-specific information from bug entry data.
    
    This class handles the parsing of bug entries to extract:
    - File name and module name 
    - Verilog unified diff
    - Provides consistent access to bug-related data
    """

    def __init__(self, bug_entry: Dict[str, Any], bug_index: int = 0):
        """
        Initialize BugInfo from a bug entry dictionary.
        
        Args:
            bug_entry: Dictionary containing bug information
            bug_index: Index of this bug in the processing sequence
        """
        self.bug_entry = bug_entry
        self.bug_index = bug_index
        
        # Extract core information - exactly matching original logic
        self.file_name = bug_entry.get('file', 'unknown')
        self.unified_diff = bug_entry.get('unified_diff', '')
        
        # Extract module name from file name (remove .sv extension) - matches line 2876
        self.module_name = os.path.splitext(self.file_name)[0] if self.file_name else None
        
    def get_display_name(self) -> str:
        """Get a display-friendly name for this bug."""
        return f"Bug #{self.bug_index + 1}: {self.file_name}"
    
    def has_verilog_diff(self) -> bool:
        """Check if this bug has a non-empty verilog diff."""
        return bool(self.unified_diff.strip())
    
    def print_debug_info(self) -> None:
        """Print debug information about this bug - matches original debug output."""
        print(f'\n🔄 Processing {self.get_display_name()}')
        print('✅ Step 3: Per-Bug Processing - START')
        
        # Show verilog_diff as requested - matches original format exactly
        print('=' * 60)
        print('📋 [DEBUG] Verilog diff from input:')
        print(self.unified_diff)
        print('=' * 60)
    
    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary for result reporting."""
        return {
            'bug_index': self.bug_index,
            'file_name': self.file_name,
            'module_name': self.module_name,
            'unified_diff': self.unified_diff,
            'has_verilog_diff': self.has_verilog_diff()
        }