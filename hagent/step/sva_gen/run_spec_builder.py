#!/usr/bin/env python3
import os
import re
import glob
import yaml
import argparse

# Import from the separate builder module
from hagent.tool.spec_builder import RtlSpecBuilder, refine_spec_markdown

def is_valid_rtl(file):
    print(f"[DEBUG] Checking if file is valid RTL: {file}")
    return file.endswith(('.sv', '.v')) and not file.endswith('_pkg.sv')

def merge_config(args, config_file):
    print(f"[DEBUG] Merging config from: {config_file}")
    if not os.path.exists(config_file):
        print(f"[ERROR] Config file '{config_file}' not found.")
        return args
    with open(config_file) as f:
        file_args = yaml.safe_load(f) or {}
    for key, value in file_args.items():
        if hasattr(args, key) and getattr(args, key) in (None, [], ""):
            print(f"[DEBUG] Overriding argument {key} with value {value}")
            setattr(args, key, value)
    return args

def run_single(args):
    if not args.top:
        print("[❌] Please provide --top for single mode.")
        return

    os.makedirs(args.out, exist_ok=True)
    json_path = os.path.join(args.out, f"{args.top}_ast.json")
    spec_path = os.path.join(args.out, f"{args.top}_spec.md")

    builder = RtlSpecBuilder(
        slang_bin=args.slang,
        rtl_dir=args.rtl,
        top_module=args.top,
        out_json=json_path,
        output_md=spec_path,
        include_dirs=args.include,
        defines=args.defines,
        llm_conf=args.llm_conf,
        disable_analysis=not args.enable_analysis,  # default True unless flag on
    )

    print(f"[🔎] Processing single RTL from directory: {args.rtl}")
    all_files = builder.collect_rtl_files()
    req_files = builder.resolve_required_files(args.top, all_files)

    if not builder.generate_ast_from_slang(req_files):
        print(f"[❌] Slang failed for {args.rtl}. No spec generated.")
        return

    ast_data = builder.read_ast(json_path)
    top_ast = builder.find_top_module(ast_data, args.top)
    if not top_ast:
        print("[❌] Top module not found in AST.")
        return

    blocks = builder.extract_fsm_blocks(top_ast)
    if not blocks:
        print("[⚠️] No FSM blocks found.")
        return

    builder.write_fsm_spec(blocks, spec_path, args.top, {})
    print(f"[✅] Wrote spec: {spec_path}")

    # Refinement step (clean names; optionally filter to only the top source)
    if args.refine:
        top_src_guess = f"{args.top}.sv" if args.only_top_source else None
        refine_spec_markdown(
            in_path=spec_path,
            out_path=spec_path,  # overwrite in place
            top_source_basename=top_src_guess
        )
        print(f"[✅] Refined spec: {spec_path}")

    if not args.llm_conf:
        print("[ℹ️] Proceeding without --llm-conf: spec will be written with the fallback (non-LLM) formatter.")


def run_multi(args):
    os.makedirs(args.out, exist_ok=True)
    rtl_files = [f for f in glob.glob(os.path.join(args.rtl, "**"), recursive=True) if is_valid_rtl(f)]
    print(f"[📁] Found {len(rtl_files)} RTL files for processing.")

    for rtl_file in rtl_files:
        top = os.path.splitext(os.path.basename(rtl_file))[0]
        json_path = os.path.join(args.out, f"{top}_ast.json")
        spec_path = os.path.join(args.out, f"{top}_spec.md")

        print(f"\n[⚙️] Processing {top} from {rtl_file}")

        builder = RtlSpecBuilder(
            slang_bin=args.slang,
            rtl_dir=args.rtl,
            top_module=top,
            out_json=json_path,
            output_md=spec_path,
            include_dirs=args.include,
            defines=args.defines,
            llm_conf=args.llm_conf,
            disable_analysis=not args.enable_analysis,
        )

        all_files = builder.collect_rtl_files()
        req_files = builder.resolve_required_files(top, all_files)

        if not builder.generate_ast_from_slang(req_files):
            print(f"[❌] Failed to generate AST for {top}")
            continue

        ast_data = builder.read_ast(json_path)
        top_ast = builder.find_top_module(ast_data, top)
        if not top_ast:
            print(f"[❌] Top module '{top}' not found in AST.")
            continue

        blocks = builder.extract_fsm_blocks(top_ast)
        if not blocks:
            print(f"[⚠️] No FSM blocks found for {top}.")
            continue
        

        builder.write_fsm_spec(blocks, spec_path, top, {})
        print(f"[✅] Wrote spec: {spec_path}")

        if args.refine:
            top_src_guess = f"{top}.sv" if args.only_top_source else None
            refine_spec_markdown(
                in_path=spec_path,
                out_path=spec_path,
                top_source_basename=top_src_guess
            )
            print(f"[✅] Refined spec: {spec_path}")

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=["single", "multi"], default="single")
    parser.add_argument("--slang", required=True)
    parser.add_argument("--llm-conf", required=False)
    parser.add_argument("--rtl", required=True)
    parser.add_argument("--top", help="Top module (for single mode)")
    parser.add_argument("--include", nargs="*", default=[])
    parser.add_argument("--defines", nargs="*", default=[])
    parser.add_argument("--out", default="out_rtl_spec")
    parser.add_argument("-f", "--config-file", help="Optional config file containing all CLI inputs")

    # Refinement options
    parser.add_argument("--refine", action="store_true", help="Refine the written spec (clean names, optional top-only)")
    parser.add_argument("--only-top-source", action="store_true",
                        help="When refining, keep only the top module's source file section (assumes <top>.sv)")
    parser.add_argument("--enable-analysis", action="store_true",
                        help="Run slang with analysis enabled (more complete AST).")

    args, _ = parser.parse_known_args()

    print(f"[DEBUG] Arguments after parsing: {args}")

    if args.config_file:
        args = merge_config(args, args.config_file)

    args.rtl = os.path.expanduser(args.rtl)
    print(f"[DEBUG] Expanded RTL path: {args.rtl}")
    os.makedirs(args.out, exist_ok=True)

    if args.mode == "single":
        print(f"[DEBUG] Running in 'single' mode.")
        if not args.top:
            print("[❌] Please provide --top for single mode.")
            return
        run_single(args)
    else:
        print(f"[DEBUG] Running in 'multi' mode.")
        run_multi(args)

if __name__ == "__main__":
    print("[DEBUG] Starting the script.")
    main()
