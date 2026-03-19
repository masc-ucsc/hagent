# See LICENSE for details
"""
Field group definitions for the frequency optimization pipeline.

Design principles:
1. Fields are grouped by LOGICAL CONCERN, not by step
2. Each group is a small, focused Pydantic model for configuration
3. Steps parse only the config groups they need
4. Step outputs are plain YAML fields (not Pydantic models)
5. YAML is the contract between steps

Usage in steps:
    # Parse configuration (validates required fields)
    benchmark = BenchmarkConfig.from_data(data, 'benchmark')
    tools = ToolsConfig.from_data(data, 'tools')

    # Read output from previous step
    netlist = require_field(data, 'synthesis.netlist_path')

    # Write output for next step
    set_field(output, 'sta.frequency_mhz', 450.5)
"""

from __future__ import annotations

from typing import Optional, List, Dict, Any, Self
from pydantic import BaseModel, Field


# =============================================================================
# YAML Field Helpers
# =============================================================================


def get_field(data: Dict, field_path: str, default: Any = None) -> Any:
    """
    Get a nested field from YAML data.

    Args:
        data: The pipeline data dict
        field_path: Dot-separated path (e.g., 'synthesis.netlist_path')
        default: Value to return if field is missing

    Returns:
        The field value, or default if not found

    Usage:
        netlist = get_field(data, 'synthesis.netlist_path')
        tag = get_field(data, 'synthesis.tag', 'baseline')
    """
    keys = field_path.split('.')
    val = data
    for key in keys:
        if not isinstance(val, dict) or key not in val:
            return default
        val = val[key]
    return val


def require_field(data: Dict, field_path: str) -> Any:
    """
    Require a nested field exists in YAML data.

    Args:
        data: The pipeline data dict
        field_path: Dot-separated path (e.g., 'synthesis.netlist_path')

    Returns:
        The field value

    Raises:
        ValueError: If field is missing

    Usage:
        netlist = require_field(data, 'synthesis.netlist_path')
    """
    val = get_field(data, field_path)
    if val is None:
        raise ValueError(f"Required field '{field_path}' missing from YAML")
    return val


def set_field(data: Dict, field_path: str, value: Any) -> Dict:
    """
    Set a nested field in YAML data.

    Creates intermediate dicts as needed. Mutates and returns data.

    Args:
        data: The pipeline data dict (will be mutated)
        field_path: Dot-separated path (e.g., 'synthesis.netlist_path')
        value: Value to set

    Returns:
        The mutated data dict

    Usage:
        set_field(output, 'synthesis.netlist_path', '/path/to/netlist.v')
        set_field(output, 'sta.frequency_mhz', 450.5)
    """
    keys = field_path.split('.')
    d = data
    for key in keys[:-1]:
        if key not in d:
            d[key] = {}
        d = d[key]
    d[keys[-1]] = value
    return data


# =============================================================================
# Base Class for Configuration Groups
# =============================================================================


class ConfigGroup(BaseModel):
    """Base class for configuration field groups."""

    class Config:
        extra = 'forbid'  # Raise error on unexpected fields

    @classmethod
    def from_data(cls, data: Dict[str, Any], key: str) -> Self:
        """
        Parse this config group from pipeline data.

        Args:
            data: The full pipeline data dict
            key: The nested key (e.g., 'benchmark', 'tools')

        Returns:
            Validated config group instance

        Raises:
            ValueError: If required section is missing
        """
        subset = data.get(key)
        if subset is None:
            raise ValueError(f"Required config section '{key}' missing from YAML")
        return cls(**subset)

    @classmethod
    def from_data_optional(cls, data: Dict[str, Any], key: str) -> Optional[Self]:
        """Parse this config group, returning None if section is missing."""
        subset = data.get(key)
        if subset is None:
            return None
        try:
            return cls(**subset)
        except Exception:
            return None


# =============================================================================
# Configuration Groups (static, provided in initial YAML)
# =============================================================================


class BenchmarkConfig(ConfigGroup):
    """
    Benchmark identification - used by most steps.

    YAML structure:
        benchmark:
          name: "PipelineDino"
          top_module: "CPU"
          synth_top_module: "CPU"  # Optional, defaults to top_module
          output_module: "CPU"  # Optional, final renamed module in netlist
          hagent_config_yaml: "/path/to/hagent_config.yaml"  # Optional, for cli_locator
          hagent_profile_name: "profile_name"  # Optional, for cli_locator --name
    """

    name: str = ''
    top_module: str
    synth_top_module: Optional[str] = None
    output_module: Optional[str] = None
    hagent_config_yaml: Optional[str] = None
    hagent_profile_name: Optional[str] = None

    @property
    def effective_synth_top(self) -> str:
        """Get synthesis top module, falling back to top_module."""
        return self.synth_top_module or self.top_module

    @property
    def effective_output_module(self) -> str:
        """Get output module name, falling back to effective_synth_top."""
        return self.output_module or self.effective_synth_top


class RTLSourceConfig(ConfigGroup):
    """
    RTL source configuration - used by synthesis, extract_critical.

    YAML structure:
        rtl:
          source_dir: the RTL source code directory "/path/to/rtl"
          manifest_file: the manifest file "/path/to/manifest_file"
          file_patterns: ["*.sv", "*.v"]
          standalone_files: the standalone *.sv/*.v files to be included in elab/synth
    """

    source_dir: str
    manifest_file: str
    file_patterns: List[str] = Field(default_factory=lambda: ['*.sv', '*.v'])
    standalone_files: Optional[List[str]] = None
    hierarchy_file: str


class ToolsConfig(ConfigGroup):
    """
    External tool paths and config - used by synthesis, STA, LEC.

    YAML structure:
        tools:
          liberty_file: "/path/to/lib.lib"
          elab_method: "slang"
          run_synalign: "false"
    """

    liberty_file: str = ''
    elab_method: str = 'auto'
    run_synalign: bool = False
    lgshell_path: Optional[str] = None
    open_ware_path: Optional[str] = None


class ThresholdsConfig(ConfigGroup):
    """
    Loop thresholds - used by orchestrator and optimization steps.

    YAML structure:
        thresholds:
          compile_fix_max: 3
          lec_fix_max: 3
          freq_refine_max: 3
          optimize_redo_max: 5
          min_improvement_pct: 5.0
    """

    compile_fix_max: int = 3
    lec_fix_max: int = 3
    freq_refine_max: int = 3
    optimize_redo_max: int = 5
    arch_refine_max: int = 1
    min_improvement_pct: float = 5.0


class LLMConfig(ConfigGroup):
    """
    LLM configuration - used by optimization step.

    All agents (architecture_timing_optimizer, module_timing_optimizer,
    syntax_fixer, lec_fixer) share a single conf_file.  LLM_wrap looks
    up its section by `name`.

    YAML structure:
        llm:
          conf_file: "/path/to/llm_agents.yaml"
          max_num_candidates: 5
    """

    conf_file: str = ''
    max_num_candidates: int = 5


class StorageConfig(ConfigGroup):
    """
    Output storage configuration - used by most steps.

    YAML structure:
        storage:
          output_dir: "/path/to/output"
          memory_db_dir: "/path/to/memory_db"
    """

    output_dir: str
    memory_db_dir: str
