import os
import shutil
import tempfile
import subprocess
import fnmatch
import difflib
from typing import Optional, List, Dict, Tuple, Any
from datetime import datetime

from ruamel.yaml import YAML
from ruamel.yaml.scalarstring import LiteralScalarString


class File_manager:
    """
    Manages an overlay filesystem of files (via fuseoverlaps), tracks in-memory edits,
    and exports/imports patches as unified diffs in YAML.
    """

    overlay_directory: str
    error_message: str

    def __init__(self, cwd: Optional[str] = ".") -> None:
        """
        Create a new overlay with overlay root (temp directory).
        Initializes internal state; does not scan or apply anything yet.
        """
        self.cwd = cwd
        self.overlay_directory = tempfile.mkdtemp(prefix="file_manager_")
        self.error_message = ""
        self.tracked_files: List[str] = []
        self._original_contents: Dict[str, List[str]] = {}
        self._yaml = YAML()
        self._yaml.indent(mapping=2, sequence=4, offset=2)

    def setup(self) -> bool:
        """
        Verify fuseoverlaps (and any deps) are available.
        Returns True on success; on failure, set `error_message` and return False.
        """
        return True

    def add_dir(
        self,
        dir: str,
        *,
        recursive: bool = False,
        ext: Optional[str] = None
    ) -> None:
        """
        Add all files in `dir` (filtered by extension glob `ext`) into the overlay.
        Does not raise; errors recorded in `error_message`.
        """
        try:
            if recursive:
                for root, _, files in os.walk(dir):
                    for fn in files:
                        if ext is None or fnmatch.fnmatch(fn, ext):
                            self._copy_and_snapshot(os.path.join(root, fn), fn)
            else:
                for fn in os.listdir(dir):
                    src = os.path.join(dir, fn)
                    if os.path.isfile(src) and (ext is None or fnmatch.fnmatch(fn, ext)):
                        self._copy_and_snapshot(src, fn)
        except Exception as e:
            self.error_message = str(e)

    def add_files(self, files: List[str]) -> None:
        """
        Add a given list of existing file paths into the overlay for tracking.
        """
        for path in files:
            try:
                fn = os.path.basename(path)
                self._copy_and_snapshot(path, fn)
            except Exception as e:
                self.error_message = str(e)

    def add_file(self, filename: str, content: str) -> None:
        """
        Create a new file `filename` in the overlay with the given text content.
        """
        dest = os.path.join(self.overlay_directory, filename)
        os.makedirs(os.path.dirname(dest), exist_ok=True)
        with open(dest, "w", encoding="utf-8") as f:
            f.write(content)
        lines = content.splitlines(keepends=True)
        self._original_contents[filename] = lines
        if filename not in self.tracked_files:
            self.tracked_files.append(filename)

    def load_yaml(self, yaml_file: str, name: str) -> bool:
        """
        Read a HAgent-style patch YAML and apply all diffs/new files into the overlay.
        Only read `name` sub entries.
        Returns False on parse/apply error (use `error_message`).
        """
        try:
            with open(yaml_file) as f:
                data = self._yaml.load(f)
            entry = data.get(name)
            if not entry:
                self.error_message = f"No entry named {name}"
                return False
            for pat in entry.get("patches", []):
                fn = pat["filename"]
                diff = pat.get("diff", "")
                patched = list(difflib.restore(diff.splitlines(keepends=True), 2))
                dest = os.path.join(self.overlay_directory, fn)
                os.makedirs(os.path.dirname(dest), exist_ok=True)
                with open(dest, "w", encoding="utf-8") as outf:
                    outf.writelines(patched)
                self._original_contents.setdefault(fn, [])
                if fn not in self.tracked_files:
                    self.tracked_files.append(fn)
            return True
        except Exception as e:
            self.error_message = str(e)
            return False

    def set_working_directory(self, path: str) -> None:
        """
        Change the virtual cwd for subsequent `run` calls. Default is “.”.
        """
        self.cwd = path

    def run(self, command: str) -> Tuple[int, str, str]:
        """
        Execute `command` against the overlay (never touching real disk).
        Returns (exit_code, stdout, stderr).
        """
        cwd = os.path.join(self.overlay_directory, self.cwd)
        try:
            proc = subprocess.Popen(
                command,
                shell=True,
                cwd=cwd,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
            out, err = proc.communicate()
            code = proc.returncode
        except Exception as e:
            self.error_message = str(e)
            return -1, "", str(e)
        for root, _, files in os.walk(self.overlay_directory):
            for fn in files:
                rel = os.path.relpath(os.path.join(root, fn), self.overlay_directory)
                if rel not in self.tracked_files:
                    self.tracked_files.append(rel)
        return code, out.decode("utf-8", errors="ignore"), err.decode("utf-8", errors="ignore")

    def get_patch_dict(self) -> Dict[str, Any]:
        """
        Return the full in-memory dict of overlay state and unified diffs.
        """
        patches = []
        for fn in self.tracked_files:
            patches.append({"filename": fn, "diff": self.get_diff(fn)})
        return {"overlay_directory": self.overlay_directory,
                "files": list(self.tracked_files),
                "patches": patches}

    def save_patches(self, yaml_file: str, name: str) -> bool:
        """
        Dump current patch-dict to YAML at `yaml_file` under top-level key `name`.
        Writes in the real cwd, not in the overlay.
        """
        def process_multiline_strings(obj):
            """
            Recursively convert strings with newlines into LiteralScalarString so that they
            are output in literal block style.
            """
            if isinstance(obj, dict):
                return {k: process_multiline_strings(v) for k, v in obj.items()}
            elif isinstance(obj, list):
                return [process_multiline_strings(item) for item in obj]
            elif isinstance(obj, str) and '\n' in obj:
                # Wrap the multiline string so that ruamel.yaml outputs it using literal block style.
                return LiteralScalarString(obj)
            return obj

        try:
            real_path = (yaml_file if os.path.isabs(yaml_file)
                         else os.path.join(os.getcwd(), yaml_file))
            data = {}
            if os.path.exists(real_path):
                data = self._yaml.load(open(real_path)) or {}
            data[name] = self.get_patch_dict()

            processed_data = process_multiline_strings(data)

            with open(real_path, "w") as outf:
                self._yaml.dump(processed_data, outf)
            return True
        except Exception as e:
            self.error_message = str(e)
            return False

    def get_file_content(self, path: str) -> str:
        """
        Return the *modified* text content of `path` in the overlay.
        If missing or binary, return empty string and set `error_message`.
        """
        fp = os.path.join(self.overlay_directory, path)
        try:
            data = open(fp, "rb").read()
        except Exception as e:
            self.error_message = str(e)
            return ""
        try:
            return data.decode("utf-8")
        except UnicodeDecodeError:
            self.error_message = "binary file"
            return ""

    def get_diff(self, filename: str) -> str:
        """
        Return a unified diff between original and modified file.
        """
        orig = self._original_contents.get(filename, [])
        mod_fp = os.path.join(self.overlay_directory, filename)
        try:
            mod_data = open(mod_fp, "rb").read().decode("utf-8")
            mod = mod_data.splitlines(keepends=True)
        except Exception:
            return ""
        fromfile = filename
        tofile = os.path.join(self.overlay_directory, filename)
        now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        diff_lines = list(difflib.unified_diff(
            orig, mod,
            fromfile, tofile,
            now, now,
            n=3
        ))
        return "".join(diff_lines)

    def get_error(self) -> str:
        """
        Return the first error message (empty if none).
        """
        return self.error_message

    def _copy_and_snapshot(self, src: str, dst: str) -> None:
        dest = os.path.join(self.overlay_directory, dst)
        os.makedirs(os.path.dirname(dest), exist_ok=True)
        shutil.copyfile(src, dest)
        try:
            data = open(dest, "rb").read().decode("utf-8")
            lines = data.splitlines(keepends=True)
        except UnicodeDecodeError:
            lines = []
        self._original_contents[dst] = lines
        if dst not in self.tracked_files:
            self.tracked_files.append(dst)

