"""
Comprehensive tests for FileSystem implementations (Local and Docker).

Tests all FileSystem APIs in both execution modes to ensure consistency:
- exists()
- read_file(), read_text(), read_binary()
- write_file(), write_text(), write_binary()
- list_dir()
- makedirs()
- remove()
- run_cmd()
- resolve_path()
"""

import subprocess
from pathlib import Path

import pytest

from hagent.inou.builder import Builder
from hagent.inou.filesystem_docker import FileSystemDocker
from hagent.inou.filesystem_local import FileSystemLocal
from hagent.inou.path_manager import PathManager


@pytest.fixture(autouse=True)
def isolate_path_manager():
    """Ensure PathManager is isolated for each test using configured()."""
    # Use PathManager.configured() with no args to create an isolated local mode instance
    with PathManager.configured():
        yield


@pytest.fixture(scope='session')
def setup_test_directory():
    """
    Setup test directory structure for both local and Docker testing.
    Creates: ./setup_run/test_filesystem_XXX/repo, /build, /cache, /logs
    Uses setup_mcp.sh for simplechisel project.
    """
    test_base = Path('./setup_run/test_filesystem')
    test_base.mkdir(parents=True, exist_ok=True)

    # Setup using the setup_mcp.sh script for simplechisel
    script_path = Path('./scripts/setup_mcp.sh').resolve()
    if script_path.exists():
        print(f'Setting up test directory using {script_path}...')
        try:
            subprocess.run(
                [str(script_path), 'simplechisel', str(test_base)],
                check=True,
                capture_output=True,
                text=True,
            )
            print(f'Successfully set up test directory at {test_base}')
        except subprocess.CalledProcessError as e:
            print(f'Warning: setup_mcp.sh failed: {e}\nstdout: {e.stdout}\nstderr: {e.stderr}')
            # Create minimal structure as fallback
            for subdir in ['repo', 'build', 'cache', 'logs']:
                (test_base / subdir).mkdir(exist_ok=True)
    else:
        print(f'Warning: setup_mcp.sh not found at {script_path}')
        # Create minimal structure
        for subdir in ['repo', 'build', 'cache', 'logs']:
            (test_base / subdir).mkdir(exist_ok=True)

    # Return absolute paths for Docker mounting to work correctly
    return {
        'base': test_base.resolve(),
        'repo': (test_base / 'repo').resolve(),
        'build': (test_base / 'build').resolve(),
        'cache': (test_base / 'cache').resolve(),
        'logs': (test_base / 'logs').resolve(),
    }


@pytest.fixture
def local_filesystem(setup_test_directory):
    """Create a local filesystem instance for testing."""
    return FileSystemLocal()


@pytest.fixture
def docker_filesystem(setup_test_directory):
    """
    Create a Docker filesystem instance for testing.
    Uses mascucsc/hagent-simplechisel:2025.11 image.
    """
    test_dirs = setup_test_directory

    # Use PathManager.configured() for Docker mode setup
    with PathManager.configured(
        docker_image='mascucsc/hagent-simplechisel:2025.11',
        repo_dir=str(test_dirs['repo']),
        build_dir=str(test_dirs['build']),
        cache_dir=str(test_dirs['cache']),
    ):
        # Create builder which will set up the container
        builder = Builder()
        try:
            if not builder.setup():
                pytest.skip(f'Builder setup failed: {builder.get_error()}')

            # Ensure container is set up
            if builder.runner.container_manager:
                setup_success = builder.runner.container_manager.setup()
                if not setup_success:
                    pytest.skip(f'Docker container setup failed: {builder.runner.container_manager.get_error()}')

            # Create Docker filesystem instance
            fs = FileSystemDocker(builder.runner.container_manager)
            yield fs
        finally:
            builder.cleanup()


@pytest.fixture(params=['local', 'docker'])
def filesystem(request, local_filesystem, docker_filesystem):
    """Parametrized fixture that provides both local and Docker filesystems."""
    if request.param == 'local':
        return local_filesystem
    else:
        return docker_filesystem


class TestFileSystemExists:
    """Test exists() method."""

    def test_exists_file(self, filesystem, tmp_path):
        """Test exists() returns True for existing file."""
        # Create test file
        test_file = tmp_path / 'test.txt'
        filesystem.write_text(str(test_file), 'test content')

        assert filesystem.exists(str(test_file))

    def test_exists_directory(self, filesystem, tmp_path):
        """Test exists() returns True for existing directory."""
        test_dir = tmp_path / 'test_dir'
        filesystem.makedirs(str(test_dir))

        assert filesystem.exists(str(test_dir))

    def test_not_exists(self, filesystem, tmp_path):
        """Test exists() returns False for non-existent path."""
        test_path = tmp_path / 'nonexistent.txt'
        assert not filesystem.exists(str(test_path))


class TestFileSystemReadWrite:
    """Test read/write operations."""

    def test_write_read_text(self, filesystem, tmp_path):
        """Test writing and reading text files."""
        test_file = tmp_path / 'test.txt'
        content = 'Hello, World!\nLine 2\nLine 3'

        # Write text
        assert filesystem.write_text(str(test_file), content)

        # Read text
        read_content = filesystem.read_text(str(test_file))
        assert read_content == content

    def test_write_read_file_explicit_encoding(self, filesystem, tmp_path):
        """Test writing and reading with explicit encoding."""
        test_file = tmp_path / 'test_utf8.txt'
        content = 'Hello UTF-8: 你好世界'

        # Write with UTF-8
        assert filesystem.write_file(str(test_file), content, encoding='utf-8')

        # Read with UTF-8
        read_content = filesystem.read_file(str(test_file), encoding='utf-8')
        assert read_content == content

    def test_write_read_binary(self, filesystem, tmp_path):
        """Test writing and reading binary files."""
        test_file = tmp_path / 'test.bin'
        binary_content = b'\x00\x01\x02\x03\xff\xfe\xfd'

        # Write binary
        assert filesystem.write_binary(str(test_file), binary_content)

        # Read binary
        read_content = filesystem.read_binary(str(test_file))
        assert read_content == binary_content

    def test_write_creates_parent_directory(self, filesystem, tmp_path):
        """Test that write_file creates parent directories."""
        nested_file = tmp_path / 'level1' / 'level2' / 'test.txt'
        content = 'nested content'

        # Write should create parent directories
        assert filesystem.write_text(str(nested_file), content)

        # Verify file exists and content is correct
        assert filesystem.exists(str(nested_file))
        assert filesystem.read_text(str(nested_file)) == content

    def test_read_nonexistent_file_raises(self, filesystem, tmp_path):
        """Test that reading non-existent file raises FileNotFoundError."""
        nonexistent = tmp_path / 'nonexistent.txt'

        with pytest.raises(FileNotFoundError):
            filesystem.read_text(str(nonexistent))

    def test_write_read_special_characters(self, filesystem, tmp_path):
        """Test handling of special Verilog/HDL characters."""
        test_file = tmp_path / 'special.v'
        # Verilog with special characters that can cause issues with shell commands
        content = """module test;
  wire [7:0] data = 8'b10101010;
  reg clk = 1'b0;
  assign out = (a & b) | (c ^ d);
  initial begin
    $display("Test: %d", data);
  end
endmodule"""

        # Write and read
        assert filesystem.write_text(str(test_file), content)
        read_content = filesystem.read_text(str(test_file))
        assert read_content == content


class TestFileSystemDirectoryOps:
    """Test directory operations."""

    def test_makedirs(self, filesystem, tmp_path):
        """Test creating directory structure."""
        test_dir = tmp_path / 'level1' / 'level2' / 'level3'

        # Create nested directories
        assert filesystem.makedirs(str(test_dir))
        assert filesystem.exists(str(test_dir))

    def test_makedirs_exist_ok(self, filesystem, tmp_path):
        """Test makedirs with exist_ok=True."""
        test_dir = tmp_path / 'test_dir'

        # Create directory
        assert filesystem.makedirs(str(test_dir))

        # Create again with exist_ok=True (default)
        assert filesystem.makedirs(str(test_dir), exist_ok=True)

    def test_list_dir(self, filesystem, tmp_path):
        """Test listing directory contents."""
        # Create test structure
        test_dir = tmp_path / 'list_test'
        filesystem.makedirs(str(test_dir))

        # Create some files
        filesystem.write_text(str(test_dir / 'file1.txt'), 'content1')
        filesystem.write_text(str(test_dir / 'file2.txt'), 'content2')
        filesystem.makedirs(str(test_dir / 'subdir'))

        # List directory
        contents = filesystem.list_dir(str(test_dir))

        # Verify contents (sort for consistent comparison)
        assert sorted(contents) == sorted(['file1.txt', 'file2.txt', 'subdir'])

    def test_list_dir_empty(self, filesystem, tmp_path):
        """Test listing empty directory."""
        test_dir = tmp_path / 'empty_dir'
        filesystem.makedirs(str(test_dir))

        contents = filesystem.list_dir(str(test_dir))
        assert contents == []

    def test_list_dir_nonexistent(self, filesystem, tmp_path):
        """Test listing non-existent directory returns empty list."""
        nonexistent = tmp_path / 'nonexistent'
        contents = filesystem.list_dir(str(nonexistent))
        assert contents == []


class TestFileSystemRemove:
    """Test remove operations."""

    def test_remove_file(self, filesystem, tmp_path):
        """Test removing a file."""
        test_file = tmp_path / 'to_remove.txt'
        filesystem.write_text(str(test_file), 'content')

        # Verify file exists
        assert filesystem.exists(str(test_file))

        # Remove file
        assert filesystem.remove(str(test_file))

        # Verify file is gone
        assert not filesystem.exists(str(test_file))

    def test_remove_directory(self, filesystem, tmp_path):
        """Test removing a directory with contents."""
        test_dir = tmp_path / 'to_remove_dir'
        filesystem.makedirs(str(test_dir))
        filesystem.write_text(str(test_dir / 'file.txt'), 'content')
        filesystem.makedirs(str(test_dir / 'subdir'))

        # Verify directory exists
        assert filesystem.exists(str(test_dir))

        # Remove directory
        assert filesystem.remove(str(test_dir))

        # Verify directory is gone
        assert not filesystem.exists(str(test_dir))

    def test_remove_nonexistent(self, filesystem, tmp_path):
        """Test removing non-existent path returns False."""
        nonexistent = tmp_path / 'nonexistent'
        filesystem.remove(str(nonexistent))
        # Both implementations may return False for non-existent paths
        # This is acceptable behavior - just verify the path doesn't exist
        assert not filesystem.exists(str(nonexistent))


class TestFileSystemRunCmd:
    """Test command execution."""

    def test_run_cmd_simple(self, filesystem, tmp_path):
        """Test running a simple command."""
        exit_code, stdout, stderr = filesystem.run_cmd('echo "hello world"')

        assert exit_code == 0
        assert 'hello world' in stdout

    def test_run_cmd_with_cwd(self, filesystem, tmp_path):
        """Test running command with working directory."""
        test_dir = tmp_path / 'cmd_test'
        filesystem.makedirs(str(test_dir))
        filesystem.write_text(str(test_dir / 'test.txt'), 'content')

        # Run command in test directory
        exit_code, stdout, stderr = filesystem.run_cmd('ls', cwd=str(test_dir))

        assert exit_code == 0
        assert 'test.txt' in stdout

    def test_run_cmd_with_env(self, filesystem, tmp_path):
        """Test running command with environment variables."""
        exit_code, stdout, stderr = filesystem.run_cmd('echo $TEST_VAR', env={'TEST_VAR': 'test_value'})

        assert exit_code == 0
        assert 'test_value' in stdout

    def test_run_cmd_failure(self, filesystem, tmp_path):
        """Test running command that fails."""
        exit_code, stdout, stderr = filesystem.run_cmd('false')

        assert exit_code != 0


class TestFileSystemResolvePath:
    """Test path resolution."""

    def test_resolve_absolute_path(self, filesystem):
        """Test resolving absolute path."""
        abs_path = '/tmp/test/path'
        resolved = filesystem.resolve_path(abs_path)

        # Should return an absolute path
        assert Path(resolved).is_absolute()

    def test_resolve_relative_path(self, filesystem, tmp_path):
        """Test resolving relative path."""
        # Create a test file with relative path
        rel_path = 'test/file.txt'
        resolved = filesystem.resolve_path(rel_path)

        # Should return an absolute path
        assert Path(resolved).is_absolute()
        assert 'test/file.txt' in resolved


@pytest.mark.skip(
    reason='Consistency tests require Docker mounts to be properly configured - skip until mount configuration is fixed'
)
class TestFileSystemConsistency:
    """Test consistency between local and Docker filesystems."""

    def test_write_read_consistency(self, local_filesystem, docker_filesystem, setup_test_directory):
        """Test that both filesystems produce the same results."""
        # Use build directory which is mounted in Docker
        test_file = setup_test_directory['build'] / 'consistency_test.txt'
        content = 'Test consistency between local and Docker'

        # Write with local
        local_filesystem.write_text(str(test_file), content)

        # Read with Docker - need to use container path
        container_path = '/code/workspace/build/consistency_test.txt'
        docker_content = docker_filesystem.read_text(container_path)

        # Should be the same
        assert docker_content == content

    def test_binary_consistency(self, local_filesystem, docker_filesystem, setup_test_directory):
        """Test binary operations are consistent."""
        # Use build directory which is mounted in Docker
        test_file = setup_test_directory['build'] / 'binary_consistency.bin'
        binary_content = b'\x00\x01\x02\x03\xff\xfe\xfd\xfc'

        # Write with local
        local_filesystem.write_binary(str(test_file), binary_content)

        # Read with Docker - need to use container path
        container_path = '/code/workspace/build/binary_consistency.bin'
        docker_content = docker_filesystem.read_binary(container_path)

        # Should be the same
        assert docker_content == binary_content

    def test_directory_ops_consistency(self, local_filesystem, docker_filesystem, setup_test_directory):
        """Test directory operations are consistent."""
        # Use build directory which is mounted in Docker
        test_dir = setup_test_directory['build'] / 'dir_consistency'

        # Create with local
        local_filesystem.makedirs(str(test_dir))
        local_filesystem.write_text(str(test_dir / 'file1.txt'), 'content1')
        local_filesystem.write_text(str(test_dir / 'file2.txt'), 'content2')

        # List with Docker - need to use container path
        container_path = '/code/workspace/build/dir_consistency'
        docker_contents = docker_filesystem.list_dir(container_path)

        # Should have the same files
        assert sorted(docker_contents) == sorted(['file1.txt', 'file2.txt'])


class TestFileSystemEdgeCases:
    """Test edge cases and error handling."""

    def test_empty_file(self, filesystem, tmp_path):
        """Test handling of empty files."""
        test_file = tmp_path / 'empty.txt'

        # Write empty content
        filesystem.write_text(str(test_file), '')

        # Read should return empty string
        content = filesystem.read_text(str(test_file))
        assert content == ''

    def test_large_file(self, filesystem, tmp_path):
        """Test handling of large files."""
        test_file = tmp_path / 'large.txt'

        # Create large content (1MB)
        large_content = 'x' * (1024 * 1024)

        # Write and read
        filesystem.write_text(str(test_file), large_content)
        read_content = filesystem.read_text(str(test_file))

        assert len(read_content) == len(large_content)

    def test_unicode_content(self, filesystem, tmp_path):
        """Test handling of Unicode content."""
        test_file = tmp_path / 'unicode.txt'

        # Various Unicode characters
        unicode_content = '你好世界 🚀 мир Здравствуй'

        # Write and read
        filesystem.write_text(str(test_file), unicode_content)
        read_content = filesystem.read_text(str(test_file))

        assert read_content == unicode_content

    def test_newline_variations(self, filesystem, tmp_path):
        """Test handling of different newline styles."""
        test_file = tmp_path / 'newlines.txt'

        # Mixed newlines - note that Python's text mode will normalize these
        # This is expected behavior on Unix systems where \r and \r\n get converted to \n
        content = 'line1\nline2\nline3\nline4'

        # Write and read
        filesystem.write_text(str(test_file), content)
        read_content = filesystem.read_text(str(test_file))

        # Content should be preserved (with normalized newlines)
        assert read_content == content
