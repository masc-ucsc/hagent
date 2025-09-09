
# HAgent I/O Module

**IMPORTANT**: External users should ONLY use `Builder` class. All other classes (`Runner`, `ContainerManager`, `PathManager`, `FileTracker`) are internal implementation details.

## Usage

```python
from hagent.inou.builder import Builder

# Always use Builder as the main entry point for IO
builder = Builder()
builder.setup()

# Direct command execution (works with/without config)
builder.run_cmd('echo "Hello"')

# Profile-based execution (only with hagent.yaml)
if builder.has_configuration():
    builder.run_api(exact_name="gcd", command_name="compile")
else:
    # Falls back to run_cmd for custom commands
    builder.run_cmd('custom build command')

# All Runner functionality available
builder.track_file('src/main.scala')
diffs = builder.get_all_diffs()

# NEW: Unified filesystem access (recommended for new code)
builder.filesystem.write_file('/path/to/file.txt', 'content')
content = builder.filesystem.read_file('/path/to/file.txt')

# Legacy file creation (maintained for backward compatibility)
builder.create_file('/path/to/file.txt', 'content')

# Always cleanup when done
builder.cleanup()
```

## API Overview

Builder provides a unified interface that works in two modes:
- **With hagent.yaml**: Full profile-based API execution via `run_api()` + direct execution via `run_cmd()`
- **Without hagent.yaml**: Direct execution via `run_cmd()` only, `run_api()` returns helpful error

Key methods:
- `run_cmd(command, cwd='.', env=None, quiet=False)` - Execute commands directly
- `run_api(exact_name=None, title_query=None, command_name='', ...)` - Execute profile-based APIs
- `track_file(path)` / `track_dir(path, ext_filter=None)` - File tracking
- `get_all_diffs(ext_filter=None)` - Get file changes
- `has_configuration()` - Check if hagent.yaml is available
- `list_profiles()` - Show available profiles

**Filesystem Access (NEW - Recommended)**:
- `builder.filesystem.read_file(path, encoding='utf-8')` - Read file content (text or binary)
- `builder.filesystem.write_file(path, content, encoding='utf-8')` - Write file content (text or binary)
- `builder.filesystem.exists(path)` - Check if file/directory exists
- `builder.filesystem.makedirs(path)` - Create directory structure
- `builder.filesystem.list_dir(path)` - List directory contents
- `builder.filesystem.remove(path)` - Remove file or directory

**Legacy Methods (Backward Compatibility)**:
- `builder.create_file(path, content, encoding='utf-8')` - Create file (delegates to filesystem)

**Binary File Handling**:
```python
# Binary files: use encoding=None
binary_data = b'\x00\x01\x02\xFF'
builder.filesystem.write_file('file.bin', binary_data.decode('latin1'), encoding=None)
read_binary = builder.filesystem.read_file('file.bin', encoding=None).encode('latin1')
```

## Internal Architecture

- `Runner`: Unified wrapper around Executor, ContainerManager, PathManager, FileTracker
- `ContainerManager`: Docker container lifecycle management  
- `PathManager`: Path resolution and environment setup
- `FileTracker`: File change tracking and diff generation
- `Executor`: Command execution (local/docker variants)
- `FileSystem`: **NEW** - Unified file operations abstraction (LocalFileSystem/DockerFileSystem)

**Do not import or use these internal classes directly.** Use `Builder` which provides access to all functionality.

## Recent Changes (v2.0)

### FileSystem Refactoring
- **Unified Interface**: Replaced separate `read_text`, `write_text`, `read_binary`, `write_binary` with unified `read_file`/`write_file`
- **Simplified API**: Single interface for both text and binary operations using `encoding` parameter
- **Cross-Platform**: Works transparently in both local and Docker execution modes
- **Backward Compatibility**: Old methods still work but are deprecated

### Migration Guide
```python
# OLD (deprecated but still works)
filesystem.read_text(path)
filesystem.write_text(path, content)
filesystem.read_binary(path)  
filesystem.write_binary(path, data)

# NEW (recommended)
filesystem.read_file(path)                    # text with UTF-8
filesystem.write_file(path, content)          # text with UTF-8
filesystem.read_file(path, encoding=None)     # binary (returns string representation)
filesystem.write_file(path, data, encoding=None)  # binary (expects string representation)
```

### Working Directory Fixes
- Fixed `Runner.run_cmd()` to respect working directory changes made via `set_cwd()`
- Added `get_cwd()` methods to executors and container managers
- Unified working directory handling between FileSystem and Executor approaches
