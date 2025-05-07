# Example 1: basic add_file → run → diff → get_file_content
import tempfile
import os
import uuid
from hagent.tool.file_manager import File_manager

# Generate a unique filename in the current directory
temp_file_path = f"tmp_{uuid.uuid4().hex}.txt"

# Write "potato" to the file
with open(temp_file_path, 'w') as temp_file:
    temp_file.write("potato")

print(f"Created temporary file at: {temp_file_path}")

# 1. initialize and verify setup
fm = File_manager()
assert fm.setup(), fm.get_error()

# 1. Add existing files
fm.add_files([temp_file_path])

# 2. create a new text file in the overlay
fm.add_file("greeting.txt", "Hello\n")
# append a line via the virtual shell
rc, out, err = fm.run('echo "World" >> greeting.txt')
assert rc == 0, f"run failed: {err}"

rc, out, err = fm.run(f"echo \"destroyer\" > {temp_file_path}")
assert rc == 0, f"run failed: {err}"

# 3. inspect modified content
content = fm.get_file_content("greeting.txt")
assert content == "Hello\nWorld\n"

content = fm.get_file_content(temp_file_path)
assert content == "destroyer\n"
# 4. unified diff should mention our change
diff = fm.get_diff("greeting.txt")
assert "+World" in diff

# 5. export to YAML
tmp_yaml = os.path.join("example1_patches.yaml")
assert fm.save_patches(tmp_yaml, name="example1"), fm.get_error()
assert os.path.exists(tmp_yaml)

# IF I ACCESS THE FILE DIRECTLY (no run), it should see the old temp_file_path
with open(temp_file_path, 'r') as file:
    content = file.read()
    print(f"File:{temp_file_path} contents:{content}")
    assert content == "potato"
