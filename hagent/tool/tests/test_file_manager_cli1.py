import tempfile
import os
import uuid
from hagent.tool.file_manager import File_manager

# --- Host-side file setup ---
temp_file_name = f'tmp_{uuid.uuid4().hex}.txt'
temp_file_host_path = os.path.join(tempfile.gettempdir(), temp_file_name)
greeting_host_path = os.path.join(tempfile.gettempdir(), 'greeting.txt')
tmp_yaml_path = os.path.join(tempfile.gettempdir(), 'example1_patches.yaml')

# Write initial content to the host files
with open(temp_file_host_path, 'w') as temp_file:
    temp_file.write('potato')
print(f'Created temporary file at: {temp_file_host_path}')

with open(greeting_host_path, 'w') as temp_file:
    temp_file.write('Hello\n')
print(f'Created greeting file at: {greeting_host_path}')

try:
    # 1. Initialize with a specific docker image.
    fm = File_manager(image='alpine:latest')
    assert fm.setup(), fm.get_error()

    assert fm.copy_file(host_path=temp_file_host_path, container_path=temp_file_name), fm.get_error()
    assert fm.copy_file(host_path=greeting_host_path, container_path='greeting.txt'), fm.get_error()

    # Debug: Let's see what's in the container
    rc, out, err = fm.run('ls -la')
    if rc != 0:
        print(f"Container listing - RC: {rc}, OUT: {repr(out)}, ERR: {repr(err)}")

    # Debug: Check working directory
    rc, out, err = fm.run('pwd')
    if rc != 0:
        print(f"Working directory - RC: {rc}, OUT: {repr(out)}, ERR: {repr(err)}")

    # Test basic shell commands first
    rc, out, err = fm.run('echo "test"')
    if rc != 0:
        print(f"Basic echo - RC: {rc}, OUT: {repr(out)}, ERR: {repr(err)}")

    # Test file existence
    rc, out, err = fm.run('ls -la greeting.txt')
    if rc != 0:
        print(f"Check greeting.txt - RC: {rc}, OUT: {repr(out)}, ERR: {repr(err)}")

    rc, out, err = fm.run(f'ls -la {temp_file_name}')
    if rc != 0:
        print(f"Check temp file - RC: {rc}, OUT: {repr(out)}, ERR: {repr(err)}")

    # Check if files are readable
    rc, out, err = fm.run('cat greeting.txt')
    if rc != 0:
        print(f"Read greeting.txt - RC: {rc}, OUT: {repr(out)}, ERR: {repr(err)}")
    else:
        print(f"greeting.txt has: {repr(out)}")

    # Test shell availability
    rc, out, err = fm.run('which sh')
    if rc != 0:
        print(f"Shell check - RC: {rc}, OUT: {repr(out)}, ERR: {repr(err)}")

    rc, out, err = fm.run('echo $SHELL')
    if rc != 0:
        print(f"Shell variable - RC: {rc}, OUT: {repr(out)}, ERR: {repr(err)}")

    # Now try the actual commands
    rc, out, err = fm.run('echo "World" >> greeting.txt')
    if rc != 0:
        print(f"Echo append command - RC: {rc}, OUT: {repr(out)}, ERR: {repr(err)}")

    rc, out, err = fm.run('cat greeting.txt')
    if rc != 0:
        print(f"Final greeting.txt - RC: {rc}, OUT: {repr(out)}, ERR: {repr(err)}")
    else:
        print(f"Final greeting.txt has: {repr(out)}")

    if rc != 0:
        print(f"COMMAND FAILED with return code {rc}")
        print(f"stdout: {repr(out)}")
        print(f"stderr: {repr(err)}")
        print(f"Error message: {fm.get_error()}")

        # Try alternative command formats
        print("\n=== Trying alternative command formats ===")
        rc2, out2, err2 = fm.run('echo World >> greeting.txt')
        print(f"Without quotes - RC: {rc2}, OUT: {repr(out2)}, ERR: {repr(err2)}")

        rc3, out3, err3 = fm.run('/bin/echo "World" >> greeting.txt')
        print(f"Full path echo - RC: {rc3}, OUT: {repr(out3)}, ERR: {repr(err3)}")

        # Check container state
        print(f"Container state: {fm.container.status}")
        try:
            fm.container.reload()
            print(f"Container state after reload: {fm.container.status}")
        except:
            print("Failed to reload container status")

    # Continue only if first command succeeded
    if rc == 0:
        print("\n=== First command succeeded, trying second ===")
        rc, out, err = fm.run(f'echo "destroyer" > {temp_file_name}')
        print(f"Second echo command - RC: {rc}, OUT: {repr(out)}, ERR: {repr(err)}")

        if rc == 0:
            print("\n=== Reading file contents ===")
            content = fm.get_file_content('greeting.txt')
            print(f"Greeting content: {repr(content)}")
            assert content == 'Hello\nWorld\n'

            content = fm.get_file_content(temp_file_name)
            print(f"Temp file content: {repr(content)}")
            assert content == 'destroyer\n'

            # Test the remaining functionality
            print("\n=== Testing diff functionality ===")
            diff = fm.get_diff('greeting.txt')
            print(f"Diff for greeting.txt: {repr(diff)}")
            assert '+World' in diff

            # Export patches to YAML
            print("\n=== Testing patch export ===")
            assert fm.save_patches(host_path=tmp_yaml_path, name='example1'), fm.get_error()
            assert os.path.exists(tmp_yaml_path)
            print(f'Successfully saved patches to: {tmp_yaml_path}')

            # Verify the original host file remains untouched
            with open(temp_file_host_path, 'r') as file:
                content = file.read()
                print(f"Original host file '{temp_file_host_path}' still contains: '{content}'")
                assert content == 'potato'

            print("\n=== ALL TESTS PASSED! ===")

        else:
            print(f"Second command failed - RC: {rc}, ERR: {repr(err)}")
    else:
        print("Skipping remaining tests due to first command failure")

finally:
    # --- Cleanup host files ---
    print('\nCleaning up host-side temporary files...')
    for path in [temp_file_host_path, greeting_host_path, tmp_yaml_path]:
        if os.path.exists(path):
            os.remove(path)
            print(f'Removed {path}')


