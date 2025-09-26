
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
builder.filesystem.write_text('/path/to/file.txt', 'content')
content = builder.filesystem.read_text('/path/to/file.txt')

# Convenient file creation (UTF-8 text files)
builder.write_text('/path/to/file.txt', 'content')

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
- `builder.filesystem.read_text(path)` - Read text file content (UTF-8)
- `builder.filesystem.write_text(path, content)` - Write text file content (UTF-8)
- `builder.filesystem.read_binary(path)` - Read binary file content
- `builder.filesystem.write_binary(path, content)` - Write binary file content
- `builder.filesystem.read_file(path, encoding)` - Read with explicit encoding
- `builder.filesystem.write_file(path, content, encoding)` - Write with explicit encoding
- `builder.filesystem.exists(path)` - Check if file/directory exists
- `builder.filesystem.makedirs(path)` - Create directory structure
- `builder.filesystem.list_dir(path)` - List directory contents
- `builder.filesystem.remove(path)` - Remove file or directory

**Binary File Handling**:
```python
# Binary files: use convenience methods
binary_data = b'\x00\x01\x02\xFF'
builder.filesystem.write_binary('file.bin', binary_data)
read_binary = builder.filesystem.read_binary('file.bin')

# Or explicitly with encoding=None
builder.filesystem.write_file('file.bin', binary_data.decode('latin1'), encoding=None)
read_binary = builder.filesystem.read_file('file.bin', encoding=None).encode('latin1')
```

## Internal Architecture

- `Runner`: Unified wrapper around Executor, ContainerManager, PathManager, FileTracker
- `ContainerManager`: Docker container lifecycle management  
- `PathManager`: Path resolution and environment setup
- `FileTracker`: File change tracking and diff generation
- `Executor`: Command execution (local/docker variants)
- `FileSystem`: Unified file operations abstraction (LocalFileSystem/DockerFileSystem)

**Do not import or use these internal classes directly.** Use `Builder` which provides access to all functionality.

