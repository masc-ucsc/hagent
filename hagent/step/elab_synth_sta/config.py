# See LICENSE for details

from typing import Any, Dict, List, Optional, Self

from pydantic import BaseModel, model_validator

from hagent.inou.path_manager import PathManager
from hagent.runner.config import lookup, set_field  # noqa: F401 – re-exported for workflow steps


def get_field(data: Dict, field_path: str) -> Any:
    """Get a nested field from YAML data.  Raises ValueError on miss."""
    val = lookup(data, field_path)
    if val is None:
        raise ValueError(f"Required field '{field_path}' missing")
    return val


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
        try:
            return cls(**subset)
        except Exception as e:
            raise ValueError(f"Invalid config for '{key}': {e}") from e


class DesignConfig(ConfigGroup):
    """Chip design configuration"""

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


class RTLConfig(ConfigGroup):
    """RTL file, structure, etc. related configuration"""

    source_dir: str = ''
    manifest_file: Optional[str] = None
    standalone_files: Optional[List[str]] = None
    hierarchy_file: Optional[str] = None
    elab_method: Optional[str] = 'auto'
    elab_file: Optional[str] = None
    netlist_file: Optional[str] = None

    @model_validator(mode='after')
    def _default_source_dir(self) -> Self:
        if not self.source_dir:
            self.source_dir = str(PathManager().repo_dir)
        return self


class StorageConfig(ConfigGroup):
    """Output, database, etc. storage configuration"""

    output_dir: str
    memory_db_dir: Optional[str] = None
    # Tag to store the elab/synth/STA's result
    tag: Optional[str] = None


class ToolsConfig(ConfigGroup):
    """
    External tool paths and config - used by synthesis, STA, LEC.

    YAML structure:
        tools:
          liberty_file: "/path/to/lib.lib"
          elab_method: "slang"
          run_synalign: "false"
    """

    liberty_file: Optional[str] = None
    lgshell_path: Optional[str] = None
    open_ware_path: Optional[str] = None
