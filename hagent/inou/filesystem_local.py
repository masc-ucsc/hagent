"""
Local filesystem implementation for HAgent.

Provides filesystem operations that work directly on the host filesystem
for local execution mode.
"""

import os
import subprocess
import sys
from pathlib import Path
from typing import List, Dict, Tuple, Optional

from .filesystem_base import FileSystem


class FileSystemLocal(FileSystem):
    """FileSystem implementation for local execution."""

    def exists(self, path: str) -> bool:
        return os.path.exists(path)

    def read_file(self, path: str, encoding: Optional[str] = 'utf-8') -> str:
        try:
            if encoding is None:
                # Binary mode - return content as string representation of bytes
                with open(path, 'rb') as f:
                    return f.read().decode('latin1')  # Use latin1 for byte preservation
            else:
                # Text mode
                with open(path, 'r', encoding=encoding) as f:
                    return f.read()
        except IOError as e:
            raise FileNotFoundError(f'Cannot read {path}: {e}')

    def write_file(self, path: str, content: str, encoding: Optional[str] = 'utf-8') -> bool:
        try:
            # Ensure parent directory exists
            parent = os.path.dirname(path)
            if parent:
                os.makedirs(parent, exist_ok=True)

            if encoding is None:
                # Binary mode - content should be string representation of bytes
                with open(path, 'wb') as f:
                    f.write(content.encode('latin1'))  # Use latin1 for byte preservation
            else:
                # Text mode
                with open(path, 'w', encoding=encoding) as f:
                    f.write(content)
            return True
        except IOError:
            return False

    def list_dir(self, path: str) -> List[str]:
        try:
            return os.listdir(path)
        except OSError:
            return []

    def makedirs(self, path: str, exist_ok: bool = True) -> bool:
        try:
            os.makedirs(path, exist_ok=exist_ok)
            return True
        except OSError:
            return False

    def remove(self, path: str) -> bool:
        try:
            if os.path.isdir(path):
                import shutil

                shutil.rmtree(path)
            else:
                os.remove(path)
            return True
        except OSError:
            return False

    def run_cmd(
        self, command: str, cwd: str = '.', env: Optional[Dict[str, str]] = None, quiet: bool = True
    ) -> Tuple[int, str, str]:
        """Execute command locally."""
        try:
            # Merge environment variables
            full_env = os.environ.copy()
            if env:
                full_env.update(env)

            # Always capture output to ensure tests work properly
            result = subprocess.run(
                command,
                shell=True,
                cwd=cwd,
                env=full_env,
                capture_output=True,
                text=True,
                timeout=300,  # 5 minute default timeout
            )

            # For non-quiet mode, also print to console for interactive use
            if not quiet:
                if result.stdout:
                    print(result.stdout, end='')
                if result.stderr:
                    print(result.stderr, end='', file=sys.stderr)

            return result.returncode, result.stdout, result.stderr

        except subprocess.TimeoutExpired:
            return -1, '', f'Command timed out: {command}'
        except Exception as e:
            return -1, '', f'Command failed: {e}'

    def resolve_path(self, path: str) -> str:
        """Resolve to absolute local path."""
        return str(Path(path).resolve())
