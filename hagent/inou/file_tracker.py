"""
File tracking facade that selects appropriate implementation.

Provides a unified interface for file tracking that automatically selects between
local git-based tracking and Docker in-memory tracking based on the execution mode.
"""

from typing import Optional, Set, Dict, Any

from .path_manager import PathManager
from .filesystem import FileSystem
from .file_tracker_local import FileTrackerLocal
from .file_tracker_docker import FileTrackerDocker


class FileTracker:
    """
    Facade that selects Local or Docker file tracker implementation.
    """

    def __init__(self, path_manager: PathManager, container_manager=None, filesystem: Optional[FileSystem] = None):
        """
        Initialize FileTracker with optional FileSystem for unified operations.

        Args:
            path_manager: PathManager instance
            container_manager: Optional ContainerManager for Docker mode
            filesystem: Optional FileSystem for unified file operations
        """
        self.filesystem = filesystem

        # Keep existing implementation as fallback
        if path_manager.execution_mode == 'docker' and container_manager is not None:
            self._impl = FileTrackerDocker(path_manager, container_manager)
        else:
            self._impl = FileTrackerLocal(path_manager, container_manager)

    # Delegate API
    def cleanup(self) -> None:
        return self._impl.cleanup()

    def track_file(self, file_path: str) -> bool:
        return self._impl.track_file(file_path)

    def track_dir(self, dir_path: str, ext_filter: Optional[str] = None) -> bool:
        return self._impl.track_dir(dir_path, ext_filter)

    def get_tracked_files(self, ext_filter: Optional[str] = None) -> Set[str]:
        return self._impl.get_tracked_files(ext_filter)

    def get_diff(self, file_path: str) -> str:
        return self._impl.get_diff(file_path)

    def get_all_diffs(self, ext_filter: Optional[str] = None) -> Dict[str, str]:
        return self._impl.get_all_diffs(ext_filter)

    def get_patch_dict(self) -> Dict[str, Any]:
        return self._impl.get_patch_dict()

    def __enter__(self):
        self._impl.__enter__()
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        return self._impl.__exit__(exc_type, exc_val, exc_tb)

    def __del__(self) -> None:
        try:
            self.cleanup()
        except Exception:
            pass

    def __getattr__(self, name):
        # Delegate unknown attributes to underlying implementation
        return getattr(self._impl, name)
