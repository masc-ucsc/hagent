import unittest

import tempfile
import os
from ruamel.yaml import YAML
from hagent.tool.file_manager import File_manager


class test_diagnostics(unittest.TestCase):
    # prepare a temp dir with mixed files
    def test_prepare_temp_director(self):
        with tempfile.TemporaryDirectory() as tmpd:
            paths = {'keep.cpp': 'int main() { return 0; }\n', 'skip.txt': 'just text\n'}
            for fn, txt in paths.items():
                with open(os.path.join(tmpd, fn), 'w') as f:
                    f.write(txt)

            fm = File_manager()
            assert fm.setup(), fm.get_error()

            # only grab .cpp files
            fm.add_dir(tmpd, ext='*.cpp', recursive=False)

            pd = fm.get_patch_dict()
            # 'keep.cpp' tracked, 'skip.txt' ignored
            assert any('keep.cpp' in f for f in pd['files'])
            assert all('skip.txt' not in f for f in pd['files'])

    # loading an existing patch YAML and continuing to edit
    def test_loading_an_existing_yaml(self):
        # 1. craft a trivial patch file
        patch_doc = {
            'preload': {
                'files': ['alpha.txt'],
                'patches': [
                    {
                        'filename': 'alpha.txt',
                        'diff': """\
--- alpha.txt
+++ alpha.txt
@@ -0,0 +1,2 @@
+foo
+bar
                    """,
                    }
                ],
            }
        }
        tmp_yaml = os.path.join(tempfile.gettempdir(), 'example3_patches.yaml')
        yaml = YAML()
        # Configure indentation (optional).
        yaml.indent(mapping=2, sequence=4, offset=2)
        with open(tmp_yaml, 'w') as f:
            yaml.dump(patch_doc, f)

        # 2. load it into a fresh File_manager
        fm = File_manager()
        assert fm.setup(), fm.get_error()
        assert fm.load_yaml(yaml_file=tmp_yaml, name="preload"), fm.get_error()

        # 3. verify that the file now exists in the overlay with the patched content
        content = fm.get_file_content('alpha.txt')
        print(f"content:{content}")
        assert content.splitlines() == ['foo', 'bar']

        # 4. make a small tweak and re-diff
        rc, _, _ = fm.run('echo "baz" >> alpha.txt')
        assert rc == 0
        new_diff = fm.get_diff('alpha.txt')
        assert '+baz' in new_diff

    # creating a binary output via run, then listing it
    def test_handle_binary_files(self):
        fm = File_manager()
        assert fm.setup(), fm.get_error()

        # 1. run a command that creates a (binary) file in the overlay
        #    here we simulate with dd writing zeros
        rc, _, err = fm.run('dd if=/dev/zero of=blob.bin bs=1 count=16')
        assert rc == 0, err

        # 2. although binary, it should appear in our patch dict
        pd = fm.get_patch_dict()
        assert 'blob.bin' in pd['files']

        # 3. get_file_content returns empty for binary, but no crash
        fm.get_file_content('blob.bin')
        #assert bin_data == ''
        # check error_message was set
        print(f"get_error has {fm.get_error()}")
        assert 'binary' in fm.get_error().lower()


if __name__ == '__main__':
    unittest.main()
