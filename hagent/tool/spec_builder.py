#!/usr/bin/env python3
import os
import re
import json
import subprocess
from typing import Any, List, Dict, Optional, Tuple
from pathlib import Path
from collections import defaultdict

# Optional (safe if missing)
try:
    from hagent.core.llm_wrap import LLM_wrap
    from hagent.core.llm_template import LLM_template
except Exception:
    LLM_wrap = None
    LLM_template = None


# ========= Refiner helpers (exported) =========
def _sanitize_fsm_name(raw: str) -> str:
    """Clean, stable FSM names (strip numeric prefixes, collapse spaces, avoid 'unnamed_fsm')."""
    if raw is None:
        return 'fsm'
    s = str(raw).strip()
    s = re.sub(r'^\s*\d+\s+', '', s)  # "12345 state_q" -> "state_q"
    s = re.sub(r'\s+', ' ', s)  # normalize whitespace
    if not s or s.lower() == 'unnamed_fsm':
        s = 'state'
    return s


def refine_spec_markdown(in_path: str, out_path: Optional[str] = None, top_source_basename: Optional[str] = None) -> str:
    """
    Read the generated spec.md and refine it:
      - Normalize FSM names in '#### FSM: ...'
      - If top_source_basename is provided, keep only sections whose
        '### Source: <file>' matches that basename.
    """
    print(f'[DEBUG] Refining spec: in_path={in_path}, out_path={out_path or in_path}, top_source={top_source_basename}')
    with open(in_path, 'r') as f:
        text = f.read()

    lines = text.splitlines()
    out_lines = []
    keep_block = True
    current_source = None

    for line in lines:
        m_src = re.match(r'^###\s+Source:\s+(.*)\s*$', line)
        if m_src:
            current_source = m_src.group(1).strip()
            if top_source_basename:
                keep_block = os.path.basename(current_source) == os.path.basename(top_source_basename)
            else:
                keep_block = True
            if keep_block:
                out_lines.append(line)
            continue

        m_fsm = re.match(r'^####\s+FSM:\s+(.*)\s*$', line)
        if m_fsm:
            raw_name = m_fsm.group(1).strip()
            clean_name = _sanitize_fsm_name(raw_name)
            if keep_block:
                out_lines.append(f'#### FSM: {clean_name}')
            continue

        if keep_block or line.startswith('## FSM Specification'):
            out_lines.append(line)

    refined = '\n'.join(out_lines)
    out_file = out_path or in_path
    with open(out_file, 'w') as f:
        f.write(refined)
    print(f'[DEBUG] Refinement complete: {out_file}')
    return out_file


# ========= Single-class Builder (exported) =========
class RtlSpecBuilder:
    def __init__(
        self,
        slang_bin: str,
        rtl_dir: str,
        top_module: str,
        out_json: str,
        output_md: Optional[str] = None,
        include_dirs: Optional[List[str]] = None,
        defines: Optional[List[str]] = None,
        llm_conf: Optional[str] = None,
        disable_analysis: bool = True,
        ast_only_ports: bool = False,  # <--- NEW
    ):
        print(f'[DEBUG] Init RtlSpecBuilder: slang={slang_bin}, rtl_dir={rtl_dir}, top={top_module}')
        self.slang_bin = slang_bin
        self.rtl_dir = os.path.abspath(rtl_dir)
        self.top_module = top_module
        self.out_json = out_json
        self.output_md = output_md or f'{top_module}_fsm_spec.md'
        self.include_dirs = [os.path.abspath(p) for p in (include_dirs or [])]
        self.defines = defines or []
        self.disable_analysis = disable_analysis
        self.ast_only_ports = ast_only_ports  # <--- NEW

        self.llm = None
        self.template_dict = {}
        if llm_conf and LLM_wrap and LLM_template:
            print(f'[DEBUG] Initializing LLM with conf: {llm_conf}')
            self.llm = LLM_wrap(name='default', conf_file=llm_conf, log_file='fsm_llm.log')
            tmpl = LLM_template(llm_conf)
            if hasattr(tmpl, 'template_dict'):
                self.template_dict = tmpl.template_dict
            else:
                raise AttributeError('LLM_template missing template_dict.')

        self._all_rtl_files: Optional[List[str]] = None
        self._module_files: Dict[str, str] = {}
        self._package_files: Dict[str, str] = {}
        self._module_deps: Dict[str, set] = defaultdict(set)

    def top_ports_from_ast(self) -> List[Dict[str, str]]:
        """
        Return ports for the *top module only*, extracted strictly from the AST JSON.
        No source fallbacks, no submodule traversal.
        """
        if not os.path.exists(self.out_json):
            raise FileNotFoundError(f'AST JSON not found at {self.out_json}. Run generate_ast_from_slang(...) or run() first.')
        ast_data = self.read_ast(self.out_json)
        top_ast = self.find_top_module(ast_data, self.top_module)
        if not top_ast:
            raise RuntimeError(f"Top module '{self.top_module}' not found in AST.")
        return self._extract_ports_from_ast(top_ast)

    def run(self) -> bool:
        print(f'[DEBUG] Running build flow for top={self.top_module}')
        all_files = self.collect_rtl_files()
        req_files = self.resolve_required_files(self.top_module, all_files)
        print(f'[DEBUG] Top files for AST generation: {req_files}')

        if not self.generate_ast_from_slang(req_files):
            print('❌ Failed to generate AST JSON')
            return False

        ast_data = self.read_ast(self.out_json)
        top_ast = self.find_top_module(ast_data, self.top_module)
        if not top_ast:
            print('❌ Top module not found in AST')
            return False

        blocks = self.extract_fsm_blocks(top_ast)
        print(f'[DEBUG] Extracted FSM blocks: {blocks}')
        self.write_fsm_spec(blocks, self.output_md, self.top_module)
        print(f'✅ FSM spec written to {self.output_md}')
        return True

    # ---- Discovery / deps ----
    def collect_rtl_files(self, extensions: Tuple[str, ...] = ('.sv', '.svh', '.v')) -> List[str]:
        if self._all_rtl_files is not None:
            return self._all_rtl_files
        print(f'[DEBUG] Collecting RTL files from directory: {self.rtl_dir}')
        files = [str(p) for p in Path(self.rtl_dir).rglob('*') if p.suffix in extensions]
        print(f'[DEBUG] Collected RTL files: {files}')
        self._all_rtl_files = files
        return files

    def find_dependencies(self, file_path: str) -> set:
        print(f'[DEBUG] Finding dependencies for file: {file_path}')
        deps = set()
        try:
            with open(file_path, 'r') as f:
                content = f.read()
                deps.update(re.findall(r'\bimport\s+([\w:]+)::\*;', content))  # packages
                deps.update(re.findall(r'`include\s+"([^"]+)"', content))  # includes
                deps.update(re.findall(r'\b([a-zA-Z_]\w*)\s*#?\s*\(', content))  # instances
        except Exception as e:
            print(f'⚠️ Could not parse {file_path}: {e}')
        print(f'[DEBUG] Dependencies found: {deps}')
        return deps

    def _index_modules_and_packages(self, rtl_files: List[str]) -> None:
        print('[DEBUG] Indexing modules and packages')
        for f in rtl_files:
            try:
                with open(f, 'r') as fh:
                    content = fh.read()
                mm = re.search(r'\bmodule\s+([a-zA-Z_]\w*)\b', content)
                if mm:
                    mod = mm.group(1)
                    self._module_files[mod] = f
                    self._module_deps[mod] = self.find_dependencies(f)
                pm = re.search(r'\bpackage\s+([a-zA-Z_]\w*)\b', content)
                if pm:
                    pkg = pm.group(1)
                    self._package_files[pkg] = f
            except Exception as e:
                print(f'[WARNING] Skipping file due to error: {f} ({e})')

        print(f'[DEBUG] Module files: {self._module_files}')
        print(f'[DEBUG] Package files: {self._package_files}')

    def resolve_required_files(self, top_module: str, rtl_files: List[str]) -> List[str]:
        print(f'[DEBUG] Resolving required files for top module: {top_module}')
        self._index_modules_and_packages(rtl_files)

        required_names = set()
        stack = [top_module]
        while stack:
            name = stack.pop()
            if name in required_names:
                continue
            required_names.add(name)
            if name in self._module_deps:
                stack.extend(self._module_deps[name])

        required_files = set()
        for name in required_names:
            if name in self._module_files:
                required_files.add(self._module_files[name])
            if name in self._package_files:
                required_files.add(self._package_files[name])

        # Resolve `include`-style deps that look like source files
        for deps in self._module_deps.values():
            for d in deps:
                if d.endswith(('.svh', '.sv', '.vh', '.v')):
                    candidates = [Path(self.rtl_dir) / d] + [Path(inc) / d for inc in self.include_dirs]
                    for c in candidates:
                        if c.exists():
                            required_files.add(str(c.resolve()))
                            break

        required_sorted = sorted(required_files)
        print(f'[DEBUG] Required files for {top_module}: {required_sorted}')
        return required_sorted

    # ---- Slang / AST ----
    def generate_ast_from_slang(self, rtl_files: List[str]) -> bool:
        print('[DEBUG] Generating AST from slang')
        rtl_files = [os.path.abspath(f) for f in rtl_files]
        cmd = [
            self.slang_bin,
            '--top',
            self.top_module,
            '--ast-json',
            self.out_json,
            '--ast-json-source-info',
            '--ignore-unknown-modules',
            '--allow-use-before-declare',
            '--diag-abs-paths',
        ]
        if self.disable_analysis:
            cmd.append('--disable-analysis')
        for inc in self.include_dirs:
            cmd += ['-I', inc]
        for d in self.defines:
            cmd.append(f'--define={d}')
        cmd += rtl_files

        print(f'[DEBUG] Include directories: {self.include_dirs}')
        print(f'[DEBUG] Defines: {self.defines}')
        print(f'[DEBUG] Running command: {" ".join(cmd)}')
        result = subprocess.run(cmd)
        if result.returncode == 0:
            print('[DEBUG] AST generation succeeded.')
        else:
            print(f'[ERROR] AST generation failed with return code: {result.returncode}')
        exists = os.path.exists(self.out_json)
        print(f'[DEBUG] out_json exists={exists}: {self.out_json}')
        return exists

    def read_ast(self, json_path: str) -> dict:
        print(f'[DEBUG] Reading AST from {json_path}')
        with open(json_path, 'r') as f:
            return json.load(f)

    def find_top_module(self, ast_data: dict, top_name: str) -> Optional[dict]:
        print(f"[DEBUG] Finding top module '{top_name}' in AST data")

        def _recursive_search(node):
            if isinstance(node, dict):
                if node.get('kind') == 'Module' and node.get('name') == top_name:
                    print(f'[DEBUG] Found top module: {node.get("name")}')
                    return node
                if node.get('kind') == 'Instance' and node.get('name') == top_name:
                    return node.get('body')
                for v in node.values():
                    res = _recursive_search(v)
                    if res:
                        return res
            elif isinstance(node, list):
                for it in node:
                    res = _recursive_search(it)
                    if res:
                        return res
            return None

        return _recursive_search(ast_data.get('design', {}).get('members', []))

    # ---- FSM extraction ----
    def parse_case_blocks(self, data: Any) -> List[Dict[str, Any]]:
        # print(f"[DEBUG] Parsing case blocks")
        case_blocks = []

        def _collect_source_span(node):
            src_file = None
            min_ln = None
            max_ln = None

            def _visit(n):
                nonlocal src_file, min_ln, max_ln
                if isinstance(n, dict):
                    sf = n.get('source_file_start') or n.get('source_file')
                    ls = n.get('source_line_start') or n.get('source_line')
                    le = n.get('source_line_end') or n.get('source_line')
                    if sf and ls and le:
                        if src_file is None:
                            src_file = sf
                        if src_file == sf:
                            min_ln = ls if min_ln is None else min(min_ln, ls)
                            max_ln = le if max_ln is None else max(max_ln, le)
                    for v in n.values():
                        _visit(v)
                elif isinstance(n, list):
                    for it in n:
                        _visit(it)

            _visit(node)
            return src_file, min_ln, max_ln

        def _find_expr_name(expr) -> Optional[str]:
            # Try to extract a readable signal path/name from the expression subtree
            def _walk(n):
                if isinstance(n, dict):
                    if n.get('kind') in ('NamedValue', 'ArbitrarySymbol'):
                        return n.get('symbol') or n.get('name')
                    for v in n.values():
                        r = _walk(v)
                        if r:
                            return r
                elif isinstance(n, list):
                    for it in n:
                        r = _walk(it)
                        if r:
                            return r
                return None

            sym = expr.get('symbol')
            return sym or _walk(expr) or expr.get('kind') or 'fsm'

        def _traverse(node: Any):
            if isinstance(node, dict):
                if node.get('kind') == 'Case':
                    expr = node.get('expr', {})
                    expr_sym = _find_expr_name(expr)
                    block_info = {
                        'expr_symbol': expr_sym,
                        'source_file': node.get('source_file_start') or node.get('source_file'),
                        'line_start': node.get('source_line_start'),
                        'line_end': node.get('source_line_end'),
                    }
                    if not (block_info['source_file'] and block_info['line_start'] and block_info['line_end']):
                        inf_sf, inf_ls, inf_le = _collect_source_span(node)
                        if inf_sf and inf_ls and inf_le:
                            # print(f"[DEBUG] Inferred source for Case: file={inf_sf}, lines={inf_ls}-{inf_le} (expr={expr_sym})")
                            block_info['source_file'] = inf_sf
                            block_info['line_start'] = inf_ls
                            block_info['line_end'] = inf_le
                        else:
                            print(f'[DEBUG] Could not infer source for Case (expr={expr_sym})')
                    case_blocks.append(block_info)
                for v in node.values():
                    _traverse(v)
            elif isinstance(node, list):
                for item in node:
                    _traverse(item)

        _traverse(data)
        # print(f"[DEBUG] Parsed case blocks: {case_blocks}")
        return case_blocks

    def extract_fsm_blocks(self, module_ast: dict) -> list:
        print('[DEBUG] Extracting FSM blocks from module AST')
        case_blocks = self.parse_case_blocks(module_ast)
        # print(f"[DEBUG] Extracted case blocks: {case_blocks}")

        seen = set()
        results = []
        for block in case_blocks:
            raw_src = block.get('source_file')
            start = block.get('line_start')
            end = block.get('line_end')

            if not (raw_src and start and end):
                print(
                    f"[DEBUG] Skipping block '{block.get('expr_symbol', 'state')}' - missing source info: "
                    f'source_file={raw_src}, line_start={start}, line_end={end}'
                )
                continue

            print(f"[DEBUG] Found block '{block.get('expr_symbol', 'state')}' @ {raw_src}:{start}-{end}")
            uid = (os.path.basename(raw_src), start, end)
            if uid in seen:
                print(f'[DEBUG] Skipping duplicate block: {uid}')
                continue
            seen.add(uid)

            block['rtl_code'] = self.extract_rtl_block(raw_src, int(start), int(end))
            block['source_file_resolved'] = raw_src
            try:
                with open(raw_src) as fr:
                    block['full_rtl_code'] = fr.read()
            except Exception as e:
                print(f'[ERROR] Could not read entire RTL from {raw_src}: {e}')
                block['full_rtl_code'] = ''

            results.append(block)

        # Sort for stable output
        results.sort(key=lambda b: (os.path.basename(b.get('source_file_resolved', '')), b.get('line_start') or 0))
        # print(f"[DEBUG] FSM blocks after processing: {results}")
        return results

    def extract_rtl_block(self, source_file_path: str, line_start: int, line_end: int) -> str:
        print(f'[DEBUG] Extracting RTL block from {source_file_path} lines {line_start}-{line_end}')
        try:
            with open(source_file_path, 'r') as f:
                lines = f.readlines()
            block = ''.join(lines[line_start - 1 : line_end]).strip()
            # print(f"[DEBUG] Extracted RTL block length={len(block)}")
            return block
        except Exception as e:
            print(f'[ERROR] Failed to extract RTL block: {e}')
            return f'// Error: {e}'

    # ---- Port & Parameter extraction ----
    def _collect_module_source_file(self, blocks: List[Dict[str, Any]], top_name: str) -> Optional[str]:
        """Best-effort guess of the module's primary source file using first FSM block."""
        if blocks:
            return blocks[0].get('source_file_resolved')
        # Fallback: search indexed module files if available
        return self._module_files.get(top_name)

    def _extract_ports_from_ast(self, module_ast: dict) -> List[Dict[str, str]]:
        """
        Robust, schema-tolerant AST traversal for ports.
        Returns: [{"name":..., "dir":"In|Out|Inout", "type":"[...] logic", "desc":"-"}]
        """
        ports: List[Dict[str, str]] = []

        def norm_dir(d):
            if not d:
                return '-'
            d = str(d).lower()
            if 'inout' in d:
                return 'Inout'
            if 'input' in d or d == 'in':
                return 'In'
            if 'output' in d or d == 'out':
                return 'Out'
            return '-'

        def packed_range_from_node(n) -> Optional[str]:
            # Try common fields used by slang for packed ranges
            # Accept either a pre-rendered text or left/right bounds
            rng = n.get('packed_range') or n.get('range') or n.get('dimensions')
            if isinstance(rng, str):
                return rng
            if isinstance(rng, dict):
                left = rng.get('left')
                r = rng.get('right')
                if left is not None and r is not None:
                    return f'[{left}:{r}]'
            return None

        def data_type_from_decl(n) -> Optional[str]:
            # Try several keys slang tends to emit
            # Examples: {"type":"logic", "signed":false, "packed_range": {...}}
            base = n.get('data_type') or n.get('type') or n.get('decl_type')
            if isinstance(base, dict):
                bt = base.get('name') or base.get('type') or base.get('kind')
                rng = packed_range_from_node(base) or packed_range_from_node(n) or ''
                return f'{rng + " " if rng else ""}{bt or "logic"}'.strip()
            if isinstance(base, str):
                rng = packed_range_from_node(n) or ''
                return f'{rng + " " if rng else ""}{base}'.strip()
            # Sometimes directly on node
            rng = packed_range_from_node(n) or ''
            if rng:
                return f'{rng} logic'
            return None

        def add_port(name, direction, dtype):
            if not name:
                return
            ports.append(
                {
                    'name': name,
                    'dir': norm_dir(direction),
                    'type': dtype or '-',
                    'desc': '-',
                }
            )

        # Depth-first walk
        def walk(n):
            if isinstance(n, dict):
                k = n.get('kind', '')
                # Common variants: "Port", "PortDeclaration", "PortSymbol"
                if k.lower().startswith('port'):
                    # Try direct fields
                    name = n.get('name') or n.get('symbol')
                    direction = n.get('direction') or n.get('dir')
                    dtype = data_type_from_decl(n)

                    # ANSI-style declarations can nest an "decl" or "declared" symbol
                    decl = n.get('decl') or n.get('declared') or n.get('declaration') or {}
                    if (not name) and isinstance(decl, dict):
                        name = decl.get('name') or decl.get('symbol')
                        dtype = dtype or data_type_from_decl(decl)
                        direction = direction or decl.get('direction')

                    if name:
                        add_port(name, direction, dtype)

                # Keep walking
                for v in n.values():
                    walk(v)
            elif isinstance(n, list):
                for it in n:
                    walk(it)

        walk(module_ast)
        # Dedup while preserving order
        seen = set()
        uniq = []
        for p in ports:
            if p['name'] not in seen:
                uniq.append(p)
                seen.add(p['name'])
        return uniq

    def _extract_parameters_from_ast(self, module_ast: dict) -> List[Dict[str, str]]:
        """
        Collect parameters / localparams (ANSI/non-ANSI). Schema tolerant.
        Returns: [{"name":..., "type":"...", "default":"...", "desc":"-"}]
        """
        params: List[Dict[str, str]] = []

        def add_param(name, ptype, default):
            if not name:
                return
            params.append(
                {
                    'name': name,
                    'type': ptype or '-',
                    'default': default if default not in (None, '') else '-',
                    'desc': '-',
                }
            )

        def render_expr(e):
            if isinstance(e, dict):
                # Try a few common representations
                return e.get('text') or e.get('value') or e.get('literal') or e.get('name')
            return str(e) if e is not None else None

        def walk(n):
            if isinstance(n, dict):
                k = n.get('kind', '').lower()
                if 'parameter' in k:  # matches "Parameter", "LocalParam", "ParamDeclaration" etc
                    name = n.get('name') or n.get('symbol')
                    ptype = None
                    dt = n.get('data_type') or n.get('type')
                    if isinstance(dt, dict):
                        ptype = dt.get('name') or dt.get('type') or dt.get('kind')
                    elif isinstance(dt, str):
                        ptype = dt
                    default = render_expr(n.get('initializer') or n.get('value') or n.get('init'))
                    if name:
                        add_param(name, ptype, default)
                for v in n.values():
                    walk(v)
            elif isinstance(n, list):
                for it in n:
                    walk(it)

        walk(module_ast)
        # Dedup by name, keep first
        seen = set()
        uniq = []
        for p in params:
            if p['name'] not in seen:
                uniq.append(p)
                seen.add(p['name'])
        return uniq

    def _extract_ports_from_source(self, source_file: Optional[str], top_name: str) -> List[Dict[str, str]]:
        """
        Fallback regex for ANSI-style module headers.
        Supports lines like:
          input  logic [31:0] a, b,
          output [3:0] y,
          inout  wire  x
        """
        if not source_file or not os.path.exists(source_file):
            return []
        try:
            with open(source_file, 'r') as f:
                text = f.read()
        except Exception:
            return []

        # Strip comments
        text = re.sub(r'/\*.*?\*/', '', text, flags=re.S)
        text = re.sub(r'//.*?$', '', text, flags=re.M)

        # Grab header between 'module top_name' and first ');'
        m = re.search(rf'\bmodule\s+{re.escape(top_name)}\s*\((.*?)\);\s*', text, flags=re.S)
        if not m:
            return []
        header = m.group(1)

        # Tokenize by semicolons/commas newlines: we’ll parse direction chunks
        decls = re.findall(r'(?mi)^\s*(input|output|inout)\s+([^;]+?)(?=,?\s*(input|output|inout|$))', header, flags=0)
        ports = []
        for dir_, rest, _next in decls:
            # Optional net/data type + optional packed range + one or multiple names
            # E.g. "logic [31:0] a, b" or "[7:0] x" or "wire y"
            # Split names at commas, keep last token for type
            type_m = re.match(r'\s*(?:(wire|logic|reg|bit|tri|signed|unsigned)\b\s*)?(?:(\[[^]]+\])\s*)?(.*)$', rest.strip())
            base_ty = None
            rng = None
            names_blob = rest
            if type_m:
                base_ty = type_m.group(1)
                rng = type_m.group(2)
                names_blob = type_m.group(3)
            dtype = ' '.join([t for t in [rng, base_ty] if t]).strip() or (rng or base_ty) or '-'
            for name in [n.strip() for n in names_blob.split(',') if n.strip()]:
                # Drop trailing array dims after name (x[3])
                name = re.sub(r'\[.*$', '', name).strip()
                if name:
                    ports.append({'name': name, 'dir': dir_.capitalize() if dir_ else '-', 'type': dtype or '-', 'desc': '-'})

        # Dedup by name
        seen = set()
        uniq = []
        for p in ports:
            if p['name'] not in seen:
                uniq.append(p)
                seen.add(p['name'])
        return uniq

    def _extract_parameters_from_source(self, source_file: Optional[str], top_name: str) -> List[Dict[str, str]]:
        """
        Fallback regex for ANSI parameter lists and body parameters.
        Matches:
           #(parameter int P = 1, localparam Q = 2)
           parameter int P = 1;
           localparam logic [3:0] Q = 4'hA;
        """
        if not source_file or not os.path.exists(source_file):
            return []
        try:
            with open(source_file, 'r') as f:
                text = f.read()
        except Exception:
            return []
        text = re.sub(r'/\*.*?\*/', '', text, flags=re.S)
        text = re.sub(r'//.*?$', '', text, flags=re.M)

        params: List[Dict[str, str]] = []

        def push(name, ty, dv):
            if not name:
                return
            params.append({'name': name, 'type': ty or '-', 'default': dv if dv not in (None, '') else '-', 'desc': '-'})

        # From parameter port list after #(
        mplist = re.search(rf'\bmodule\s+{re.escape(top_name)}\s*#\s*\((.*?)\)\s*\(', text, flags=re.S)
        if mplist:
            for kind, ty, name, dv in re.findall(
                r'(?i)\b(parameter|localparam)\s+([^,=]+?)\s+([A-Za-z_]\w*)\s*(?:=\s*([^,]+))?', mplist.group(1)
            ):
                push(name.strip(), ty.strip(), dv.strip() if dv else '-')

        # From body declarations
        for kind, ty, name, dv in re.findall(
            r'(?im)^\s*(parameter|localparam)\s+([^;=]+?)\s+([A-Za-z_]\w*)\s*(?:=\s*([^;]+))?;', text
        ):
            push(name.strip(), ty.strip(), dv.strip() if dv else '-')

        # Dedup by name
        seen = set()
        uniq = []
        for p in params:
            if p['name'] not in seen:
                uniq.append(p)
                seen.add(p['name'])
        return uniq

    def _append_interfaces_and_params(self, f, blocks: List[Dict[str, Any]], module_ast: dict, top_name: str):
        """Writes Interface Ports and Parameters sections above FSMs."""
        # Try AST first
        ports = self._extract_ports_from_ast(module_ast)
        params = self._extract_parameters_from_ast(module_ast)

        # Fallback via source
        src_guess = self._collect_module_source_file(blocks, top_name)
        if not ports:
            ports = self._extract_ports_from_source(src_guess, top_name)
        if not params:
            params = self._extract_parameters_from_source(src_guess, top_name)

        # Nothing to do?
        if not ports and not params:
            return

        # LLM tables if templates exist
        use_llm_ports = self.llm and self._has_tmpl('interface_table') and ports
        use_llm_params = self.llm and self._has_tmpl('parameter_table') and params

        if ports:
            f.write('### Interface\n\n')
            if use_llm_ports:
                try:
                    res = self.llm.inference(
                        {'ports_json': json.dumps(ports, ensure_ascii=False)}, prompt_index='interface_table'
                    )
                    if self.llm.last_error or not res or not res[0].strip():
                        raise RuntimeError(self.llm.last_error or 'empty LLM output')
                    f.write(res[0].strip() + '\n\n')
                except Exception as e:
                    print(f'[LLM] interface_table error: {e} — using fallback table.')
                    # Fallback Markdown table
                    f.write('| Port Name | Direction | Type | Description |\n|---|---|---|---|\n')
                    for p in ports:
                        f.write(f'| {p["name"]} | {p["dir"]} | {p["type"]} | - |\n')
                    f.write('\n')
            else:
                # Fallback Markdown table
                f.write('| Port Name | Direction | Type | Description |\n|---|---|---|---|\n')
                for p in ports:
                    f.write(f'| {p["name"]} | {p["dir"]} | {p["type"]} | - |\n')
                f.write('\n')

        if params:
            f.write('### Parameters\n\n')
            if use_llm_params:
                try:
                    res = self.llm.inference(
                        {'params_json': json.dumps(params, ensure_ascii=False)}, prompt_index='parameter_table'
                    )
                    if self.llm.last_error or not res or not res[0].strip():
                        raise RuntimeError(self.llm.last_error or 'empty LLM output')
                    f.write(res[0].strip() + '\n\n')
                except Exception as e:
                    print(f'[LLM] parameter_table error: {e} — using fallback table.')
                    f.write('| Name | Type | Default | Description |\n|---|---|---|---|\n')
                    for p in params:
                        f.write(f'| {p["name"]} | {p["type"]} | {p["default"]} | - |\n')
                    f.write('\n')
            else:
                f.write('| Name | Type | Default | Description |\n|---|---|---|---|\n')
                for p in params:
                    f.write(f'| {p["name"]} | {p["type"]} | {p["default"]} | - |\n')
                f.write('\n')

    def _append_interfaces_and_params_ast_only(self, f, module_ast: dict, top_name: str):
        """Writes Interface/Parameters strictly from AST of the top module (no fallbacks)."""
        if not module_ast:
            return

        ports = self._extract_ports_from_ast(module_ast)
        params = self._extract_parameters_from_ast(module_ast)

        if not ports and not params:
            return

        use_llm_ports = self.llm and self._has_tmpl('interface_table') and ports
        use_llm_params = self.llm and self._has_tmpl('parameter_table') and params

        if ports:
            f.write('### Interface\n\n')
            if use_llm_ports:
                try:
                    res = self.llm.inference(
                        {'ports_json': json.dumps(ports, ensure_ascii=False)}, prompt_index='interface_table'
                    )
                    if self.llm.last_error or not res or not res[0].strip():
                        raise RuntimeError(self.llm.last_error or 'empty LLM output')
                    f.write(res[0].strip() + '\n\n')
                except Exception as e:
                    print(f'[LLM] interface_table error: {e} — using fallback table.')
                    f.write('| Port Name | Direction | Type | Description |\n|---|---|---|---|\n')
                    for p in ports:
                        f.write(f'| {p["name"]} | {p["dir"]} | {p["type"]} | - |\n')
                    f.write('\n')
            else:
                f.write('| Port Name | Direction | Type | Description |\n|---|---|---|---|\n')
                for p in ports:
                    f.write(f'| {p["name"]} | {p["dir"]} | {p["type"]} | - |\n')
                f.write('\n')

        if params:
            f.write('### Parameters\n\n')
            if use_llm_params:
                try:
                    res = self.llm.inference(
                        {'params_json': json.dumps(params, ensure_ascii=False)}, prompt_index='parameter_table'
                    )
                    if self.llm.last_error or not res or not res[0].strip():
                        raise RuntimeError(self.llm.last_error or 'empty LLM output')
                    f.write(res[0].strip() + '\n\n')
                except Exception as e:
                    print(f'[LLM] parameter_table error: {e} — using fallback table.')
                    f.write('| Name | Type | Default | Description |\n|---|---|---|---|\n')
                    for p in params:
                        f.write(f'| {p["name"]} | {p["type"]} | {p["default"]} | - |\n')
                    f.write('\n')
            else:
                f.write('| Name | Type | Default | Description |\n|---|---|---|---|\n')
                for p in params:
                    f.write(f'| {p["name"]} | {p["type"]} | {p["default"]} | - |\n')
                f.write('\n')

    # ---- Writer ----
    def write_fsm_spec(self, blocks, output_file: str, top_name: str, submodules: Optional[Dict] = None):
        """
        Router:
          - If LLM + templates available, use the LLM writer.
          - Otherwise, use the original simple dump.
        """
        use_llm = bool(self.llm and (self._has_tmpl('fsm_specification') or self._has_tmpl('doc_sections')))
        if use_llm:
            return self.write_fsm_spec_llm(blocks, output_file, top_name)

        # --------- Original simple writer (fallback) ---------
        # print(f"[DEBUG] Writing FSM spec to {output_file} (fallback writer)")
        grouped = defaultdict(list)
        for b in blocks:
            src = os.path.basename(b.get('source_file_resolved', 'unknown'))
            grouped[src].append(b)

        with open(output_file, 'w') as f:
            f.write(f'## FSM Specification for Top Module: {top_name}\n\n')
            for src, blks in grouped.items():
                f.write(f'### Source: {src}\n\n')
                for blk in blks:
                    rtl_code = blk.get('rtl_code') or '// RTL not available'
                    title = _sanitize_fsm_name(blk.get('expr_symbol', 'state'))
                    ls, le = blk.get('line_start'), blk.get('line_end')
                    f.write(f'#### FSM: {title}\n')
                    if src and ls and le:
                        f.write(f'*Location:* `{src}:{ls}-{le}`\n\n')
                    f.write(f'```systemverilog\n{rtl_code}\n```\n\n')
        print(f'[DEBUG] FSM spec written successfully (fallback): {output_file}')

    # ---- LLM helpers ----
    def _has_tmpl(self, key: str) -> bool:
        return bool(self.template_dict and 'default' in self.template_dict and key in self.template_dict['default'])

    def _guess_states_from_rtl(self, rtl_code: str) -> List[str]:
        """
        Very light heuristic to collect case item labels:
          - Matches:  ID: , ID) : , 'default:' etc.
          - Keeps order of first appearance; unique.
        """
        if not rtl_code:
            return []
        # Strip comments (crude but helps)
        code = re.sub(r'//.*?$|/\*.*?\*/', '', rtl_code, flags=re.S)
        # Find labels followed by colon within case items
        # Handles: STATE, STATE), default
        candidates = re.findall(r'(?m)^\s*([A-Za-z_]\w*|default)\s*:', code)
        seen, ordered = set(), []
        for c in candidates:
            if c not in seen:
                seen.add(c)
                ordered.append(c)
        return ordered

    def _fsm_block_to_json(self, blk: Dict[str, Any], module_name: str) -> Dict[str, Any]:
        """Compact JSON context for a single FSM."""
        states = self._guess_states_from_rtl(blk.get('rtl_code', ''))
        fsm = {
            'module': module_name,
            'expr_symbol': blk.get('expr_symbol') or 'state',
            'source_file': os.path.basename(blk.get('source_file_resolved', '')),
            'line_start': blk.get('line_start'),
            'line_end': blk.get('line_end'),
            'states': states,  # may be empty; LLM template handles "not specified"
            'signals_seen': [],  # placeholder for future enrichments
        }
        return fsm

    def _overall_context_json(self, blocks: List[Dict[str, Any]], top_name: str) -> Dict[str, Any]:
        by_src = defaultdict(int)
        fsm_summaries = []
        for b in blocks:
            src = os.path.basename(b.get('source_file_resolved', ''))
            by_src[src] += 1
            fsm_summaries.append(
                {
                    'expr_symbol': b.get('expr_symbol') or 'state',
                    'source': src,
                    'line_start': b.get('line_start'),
                    'line_end': b.get('line_end'),
                    'state_count_guess': len(self._guess_states_from_rtl(b.get('rtl_code', ''))),
                }
            )
        return {
            'top_module': top_name,
            'sources': [{'file': k, 'fsm_count': v} for k, v in sorted(by_src.items())],
            'fsm_count': len(blocks),
            'fsms': fsm_summaries,
        }

    def write_fsm_spec_llm(self, blocks, output_file: str, top_name: str):
        """
        LLM-driven renderer:
        - Prepends 'doc_sections' if template exists
        - Adds Interface/Parameters tables (LLM or fallback)
        - For each FSM, calls 'fsm_specification' with {fsm_json}, {rtl_code}, {module_name}
        """
        if not self.llm:
            raise RuntimeError('LLM not initialized.')

        with open(output_file, 'w') as f:
            # Optional: high-level narrative
            if self._has_tmpl('doc_sections'):
                ctx = self._overall_context_json(blocks, top_name)
                try:
                    res = self.llm.inference({'context_json': json.dumps(ctx, ensure_ascii=False)}, prompt_index='doc_sections')
                    if self.llm.last_error:
                        print(f'[LLM] doc_sections error: {self.llm.last_error}')
                    elif res and res[0].strip():
                        f.write(res[0].strip() + '\n\n')
                except Exception as e:
                    print(f'[LLM] Exception in doc_sections: {e}')

            # Header
            f.write(f'## FSM Specification for Top Module: {top_name}\n\n')

            # Interfaces / Parameters (TOP AST ONLY if toggled)
            try:
                ast_data = self.read_ast(self.out_json)
                module_ast = self.find_top_module(ast_data, top_name) or {}
            except Exception as e:
                print(f'[DEBUG] Could not reload AST for interface extraction: {e}')
                module_ast = {}

            if self.ast_only_ports:
                self._append_interfaces_and_params_ast_only(f, module_ast, top_name)
            else:
                self._append_interfaces_and_params(f, blocks, module_ast, top_name)

            # Group by source for readability (sorted for stable output)
            grouped = defaultdict(list)
            for b in blocks:
                src = os.path.basename(b.get('source_file_resolved', 'unknown'))
                grouped[src].append(b)

            for src in sorted(grouped.keys()):
                blks = grouped[src]
                f.write(f'### Source: {src}\n\n')
                for blk in blks:
                    title = _sanitize_fsm_name(blk.get('expr_symbol', 'state'))
                    ls, le = blk.get('line_start'), blk.get('line_end')
                    f.write(f'#### FSM: {title}\n')
                    if src and ls and le:
                        f.write(f'*Location:* `{src}:{ls}-{le}`\n\n')

                    # Build inputs for the template
                    fsm_json = self._fsm_block_to_json(blk, top_name)
                    rtl_code = blk.get('rtl_code') or '// RTL not available'

                    # If template missing, print RTL fenced block as fallback for this FSM
                    if not self._has_tmpl('fsm_specification'):
                        f.write(f'```systemverilog\n{rtl_code}\n```\n\n')
                        continue

                    try:
                        res = self.llm.inference(
                            {'fsm_json': json.dumps(fsm_json, ensure_ascii=False), 'rtl_code': rtl_code, 'module_name': top_name},
                            prompt_index='fsm_specification',
                        )

                        if self.llm.last_error:
                            print(f'[LLM] fsm_specification error ({title}): {self.llm.last_error}')
                            f.write(f'```systemverilog\n{rtl_code}\n```\n\n')
                        elif res and res[0].strip():
                            f.write(res[0].strip() + '\n\n')
                        else:
                            print(f'[LLM] Empty output for FSM {title}; writing RTL fallback.')
                            f.write(f'```systemverilog\n{rtl_code}\n```\n\n')

                    except Exception as e:
                        print(f'[LLM] Exception for FSM {title}: {e}')
                        f.write(f'```systemverilog\n{rtl_code}\n```\n\n')

        print(f'[DEBUG] LLM FSM spec written successfully: {output_file}')
