# hagent/tool/chisel2v.py
# See LICENSE file for details
import os
import re
import subprocess
import tempfile
import shutil
from typing import Optional


class Chisel2v:
    """
    A tool to convert Chisel code to Verilog by invoking 'circt' (sbt).
    """

    def __init__(self):
        self.error_message = ''
        self._is_ready = False
        self._cached_sbt_path = None

    def setup(self, sbt_path: Optional[str] = None) -> bool:
        """
        Verifies that sbt (and by extension circt) is installed. Returns True if found,
        False otherwise. On failure, populates self.error_message and sets _is_ready=False.
        Does not raise exceptions.
        """
        self._is_ready = False
        self.error_message = ''
        # Attempt to locate sbt via system PATH or user-provided path
        # For a real system check, one might do: subprocess.run(["which", "sbt"], check=True)
        # or check if "sbt" is executable in sbt_path if provided.
        if sbt_path is not None:
            sbt_bin = os.path.join(sbt_path, 'sbt')
            if not (os.path.exists(sbt_bin) and os.access(sbt_bin, os.X_OK)):
                self.error_message = f'sbt not found or not executable at {sbt_bin}'
                return False
            self._cached_sbt_path = sbt_bin
        else:
            # Fallback to checking "sbt" in PATH
            which_result = shutil.which('sbt')
            if not which_result:
                self.error_message = 'sbt not found in PATH'
                return False
            self._cached_sbt_path = which_result
        # Optional: check if the build template file is accessible (if needed):
        # build_template_path = os.path.join(os.path.dirname(__file__), "chisel2v_build.sbt")
        # if not os.path.isfile(build_template_path):
        #     self.error_message = "Missing chisel2v_build.sbt template"
        #     return False
        self._is_ready = True
        return True

    def chisel_fix(self, chisel_code: str, classname: str) -> str:
        """
        Modifies the given chisel_code (a .scala file content) to ensure correct imports,
        references, and a top-level App for generating SystemVerilog code with ChiselStage.
        Returns the possibly modified string. Raises RuntimeError only on critical issues.
        """
        if not classname:
            raise RuntimeError('No classname provided for chisel_fix')
        # Split into lines for parsing
        lines = chisel_code.splitlines(keepends=True)
        modified_lines = []
        # 1. Check for a line that imports chisel3.util._
        import_chisel_util = 'import chisel3.util._'
        found_chisel_util = any(import_chisel_util in ln for ln in lines)
        # 2. Check for a line that imports _root_.circt.stage.ChiselStage
        import_circt_stage = 'import _root_.circt.stage.ChiselStage'
        found_circt_stage = any(import_circt_stage in ln for ln in lines)
        # Create a new set of lines with potential modifications
        last_import_idx = -1
        for idx, ln in enumerate(lines):
            if ln.strip().startswith('import '):
                last_import_idx = idx
            modified_lines.append(ln)
        # Insert missing imports after the last import or at start
        if not found_chisel_util:
            insert_idx = last_import_idx + 1 if last_import_idx != -1 else 0
            modified_lines.insert(insert_idx, import_chisel_util + '\n')
            last_import_idx += 1
        if not found_circt_stage:
            insert_idx = last_import_idx + 1 if last_import_idx != -1 else 0
            modified_lines.insert(insert_idx, import_circt_stage + '\n')
            last_import_idx += 1
        # 3. Check if there's an object that extends App
        object_extends_app_pattern = re.compile(r'\bobject\s+\w+\s+extends\s+App\b')
        object_exists = any(object_extends_app_pattern.search(ln) for ln in modified_lines)
        # If not, append the top-level snippet at the end
        if not object_exists:
            # Adding yosys options to avoid some popular systemVerilog
            snippet = (
                f'\nobject Top extends App {{\n'
                f'  ChiselStage.emitSystemVerilogFile(\n'
                f'    new {classname},\n'
                f'    firtoolOpts = Array("-disable-all-randomization","--lowering-options=disallowPackedArrays,disallowLocalVariables")\n'
                f'  )\n'
                f'}}\n'
            )
            modified_lines.append(snippet)
        # Return the modified content
        return ''.join(modified_lines)

    def generate_verilog(self, chisel_code: str, module_name: str) -> str:
        """
        Generates Verilog from the given Chisel code using circt (sbt).
        Raises RuntimeError on failure.
        chisel_code: the text of the Chisel module
        module_name: class name of the top module in the .scala file
        out_verilog: the text of the Generated Verilog
        """
        if not self._is_ready:
            raise RuntimeError('Chisel2v not ready; call setup() first')
        # Create a unique temp dir
        work_dir = tempfile.mkdtemp(dir=os.getcwd(), prefix='chisel2v_')
        print(f'Chisel2v working directory:{work_dir}')
        try:
            # Copy the build.sbt template
            template_path = os.path.join(os.path.dirname(__file__), 'chisel2v_build.sbt')
            sbt_target_path = os.path.join(work_dir, 'build.sbt')
            shutil.copyfile(template_path, sbt_target_path)
            # Prepare the source folder
            src_dir = os.path.join(work_dir, 'src', 'main', 'scala')
            os.makedirs(src_dir)
            # Fix the code (insert missing imports, etc.)
            fixed_code = self.chisel_fix(chisel_code, module_name)
            # Write the Chisel code to a .scala file
            scala_file_path = os.path.join(src_dir, f'{module_name}.scala')
            with open(scala_file_path, 'w', encoding='utf-8') as f:
                f.write(fixed_code)
            # Invoke sbt to produce SystemVerilog
            # The default "sbt run" expects a main method or an 'extends App'
            # We'll rely on the object Top extends App we inserted to produce the .sv
            cmd = [self._cached_sbt_path, 'run']
            proc = subprocess.run(cmd, cwd=work_dir, check=False, capture_output=True, text=True)
            if proc.returncode != 0:
                raise RuntimeError(f'sbt run failed:\nSTDOUT:\n{proc.stdout}\nSTDERR:\n{proc.stderr}')
            # Check if <module_name>.v was created by ChiselStage
            generated_v = os.path.join(work_dir, f'{module_name}.v')
            if not os.path.isfile(generated_v):
                # If no .v file found, maybe a .sv was generated
                generated_sv = os.path.join(work_dir, f'{module_name}.sv')
                if os.path.isfile(generated_sv):
                    # Convert .sv to .v if needed, or just rename
                    # For this example, rename the .sv to .v
                    shutil.copyfile(generated_sv, generated_v)
                else:
                    raise RuntimeError('No .v or .sv file produced by sbt run')
            with open(generated_v, 'r') as file:
                return file.read()
        except Exception as ex:
            raise RuntimeError(f'Failed to generate Verilog: {ex}') from ex
        # finally:
        # Cleanup
        # shutil.rmtree(work_dir, ignore_errors=True)
