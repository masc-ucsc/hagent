"""
Base abstract filesystem interface for HAgent.

Provides the abstract FileSystem class that concrete implementations inherit from.
"""

from abc import ABC, abstractmethod
from typing import List, Dict, Tuple, Optional


class FileSystem(ABC):
    """
    Abstract file system interface that works in both local and Docker modes.

    This eliminates the need for if/else branches based on execution mode
    by providing a unified interface for all file operations.
    """

    @abstractmethod
    def exists(self, path: str) -> bool:
        """Check if file or directory exists."""
        pass

    @abstractmethod
    def read_file(self, path: str, encoding: Optional[str] = 'utf-8') -> str:
        """Read file content. Returns text by default, or bytes if encoding=None."""
        pass

    @abstractmethod
    def write_file(self, path: str, content: str, encoding: Optional[str] = 'utf-8') -> bool:
        """Write file content. Accepts text by default, or bytes if encoding=None."""
        pass

    @abstractmethod
    def list_dir(self, path: str) -> List[str]:
        """List directory contents."""
        pass

    @abstractmethod
    def makedirs(self, path: str, exist_ok: bool = True) -> bool:
        """Create directory structure."""
        pass

    @abstractmethod
    def remove(self, path: str) -> bool:
        """Remove file or directory."""
        pass

    @abstractmethod
    def run_cmd(
        self, command: str, cwd: str = '.', env: Optional[Dict[str, str]] = None, quiet: bool = True
    ) -> Tuple[int, str, str]:
        """Execute command in the appropriate context."""
        pass

    @abstractmethod
    def resolve_path(self, path: str) -> str:
        """Resolve path to absolute form appropriate for this filesystem."""
        pass

    # Backward compatibility methods (deprecated)
    def read_text(self, path: str, encoding: str = 'utf-8') -> str:
        """Deprecated: use read_file() instead."""
        return self.read_file(path, encoding)

    def write_text(self, path: str, content: str, encoding: str = 'utf-8') -> bool:
        """Deprecated: use write_file() instead."""
        return self.write_file(path, content, encoding)

    def read_binary(self, path: str) -> bytes:
        """Deprecated: use read_file(path, encoding=None).encode('latin1') instead."""
        return self.read_file(path, encoding=None).encode('latin1')

    def write_binary(self, path: str, content: bytes) -> bool:
        """Deprecated: use write_file(path, content.decode('latin1'), encoding=None) instead."""
        return self.write_file(path, content.decode('latin1'), encoding=None)