#!/usr/bin/env python3
"""
CLI tool for testing Module_finder functionality.

Usage:
    uv run python ./hagent/tool/tests/cli_module_finder.py --diff ./tmp/diff --verilog ./tmp/build_pipelined1/ALU.sv ./tmp/src/main/scala/*/*.scala

This script demonstrates how to use the Module_finder class to match Verilog modules
from a diff against Scala/Chisel source files.
"""

import argparse
import os
import sys
import glob
from pathlib import Path

# Add the project root to the Python path
sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent))

from hagent.tool.module_finder import Module_finder, ModuleHit


def expand_glob_patterns(patterns):
    """Expand glob patterns and return list of actual file paths"""
    files = []
    for pattern in patterns:
        if '*' in pattern:
            # Use glob to expand the pattern
            expanded = glob.glob(pattern)
            files.extend(expanded)
        else:
            # Regular file path
            if os.path.exists(pattern):
                files.append(pattern)
            else:
                print(f"Warning: File not found: {pattern}")
    return files


def extract_module_name_from_verilog(verilog_file):
    """Extract the primary module name from a Verilog file"""
    if not os.path.exists(verilog_file):
        return None
        
    try:
        with open(verilog_file, 'r', encoding='utf-8') as f:
            for line in f:
                line = line.strip()
                if line.startswith('module '):
                    # Extract module name (handle parameters)
                    parts = line.split('(')[0].split()
                    if len(parts) >= 2:
                        return parts[1]
    except (IOError, OSError):
        pass
    return None


def format_file_path(file_path, base_path=None):
    """Format file path for display, making it relative to base_path if provided"""
    if base_path:
        try:
            return os.path.relpath(file_path, base_path)
        except ValueError:
            pass
    return file_path


def print_results(hits, base_path=None, verbose=False):
    """Print the module finder results in a formatted way"""
    if not hits:
        print("❌ No matching modules found.")
        return
    
    print(f"✅ Found {len(hits)} potential matches:")
    print("=" * 80)
    
    for i, hit in enumerate(hits, 1):
        confidence_bar = "█" * int(hit.confidence * 10) + "░" * (10 - int(hit.confidence * 10))
        confidence_color = "🟢" if hit.confidence >= 0.8 else "🟡" if hit.confidence >= 0.5 else "🔴"
        
        print(f"[{i}] {confidence_color} {hit.module_name}")
        print(f"    📁 File: {format_file_path(hit.file_name, base_path)}")
        print(f"    📍 Lines: {hit.start_line}-{hit.end_line}")
        print(f"    📊 Confidence: {hit.confidence:.2f} [{confidence_bar}]")
        
        if verbose and os.path.exists(hit.file_name):
            try:
                with open(hit.file_name, 'r', encoding='utf-8') as f:
                    lines = f.readlines()
                    print(f"    📖 Preview:")
                    start_idx = max(0, hit.start_line - 1)
                    end_idx = min(len(lines), hit.start_line + 3)  # Show first few lines of the module
                    for j, line in enumerate(lines[start_idx:end_idx], start=hit.start_line):
                        prefix = "    ► " if j == hit.start_line else "      "
                        print(f"{prefix}{j:4d}: {line.rstrip()}")
            except (IOError, OSError):
                pass
        
        if i < len(hits):
            print()


def main():
    parser = argparse.ArgumentParser(
        description="Find Scala/Chisel modules corresponding to Verilog modules in a diff",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Basic usage with explicit files
  python cli_module_finder.py --diff ./tmp/diff --verilog ./tmp/build_pipelined1/ALU.sv ./tmp/src/main/scala/components/alu.scala

  # Using glob patterns for Scala files
  python cli_module_finder.py --diff ./tmp/diff --verilog ./tmp/build_pipelined1/ALU.sv ./tmp/src/main/scala/*/*.scala

  # Verbose output with code previews
  python cli_module_finder.py --diff ./tmp/diff --verilog ./tmp/build_pipelined1/ALU.sv ./tmp/src/main/scala/*/*.scala --verbose

  # Find all modules mentioned in diff (no specific verilog file)
  python cli_module_finder.py --diff ./tmp/diff ./tmp/src/main/scala/*/*.scala --verbose
        """
    )
    
    parser.add_argument('--diff', required=True, help='Path to the unified diff file')
    parser.add_argument('--verilog', help='Path to the primary Verilog file (optional)')
    parser.add_argument('scala_files', nargs='+', help='Scala source files (supports glob patterns)')
    parser.add_argument('--verbose', '-v', action='store_true', help='Show code previews')
    parser.add_argument('--min-confidence', type=float, default=0.3, 
                       help='Minimum confidence threshold (default: 0.3)')
    
    args = parser.parse_args()
    
    # Validate diff file
    if not os.path.exists(args.diff):
        print(f"❌ Error: Diff file not found: {args.diff}")
        sys.exit(1)
    
    # Read diff content
    try:
        with open(args.diff, 'r', encoding='utf-8') as f:
            diff_content = f.read()
    except (IOError, OSError) as e:
        print(f"❌ Error reading diff file: {e}")
        sys.exit(1)
    
    if not diff_content.strip():
        print(f"❌ Error: Diff file is empty: {args.diff}")
        sys.exit(1)
    
    # Expand scala file patterns
    scala_files = expand_glob_patterns(args.scala_files)
    if not scala_files:
        print("❌ Error: No Scala files found matching the given patterns")
        sys.exit(1)
    
    # Extract verilog module name if provided
    verilog_module = None
    if args.verilog:
        if not os.path.exists(args.verilog):
            print(f"❌ Error: Verilog file not found: {args.verilog}")
            sys.exit(1)
        
        verilog_module = extract_module_name_from_verilog(args.verilog)
        if not verilog_module:
            print(f"⚠️  Warning: Could not extract module name from {args.verilog}")
    
    # Print summary
    print("🔍 Module Finder Analysis")
    print("=" * 80)
    print(f"📄 Diff file: {args.diff}")
    if args.verilog:
        print(f"🔧 Verilog file: {args.verilog}")
        if verilog_module:
            print(f"📦 Primary module: {verilog_module}")
    print(f"📚 Scala files: {len(scala_files)} files")
    print(f"🎯 Min confidence: {args.min_confidence}")
    print()
    
    # Show diff preview
    print("📋 Diff preview:")
    print("-" * 40)
    diff_lines = diff_content.split('\n')[:10]  # Show first 10 lines
    for line in diff_lines:
        if line.startswith('+++') or line.startswith('---'):
            print(f"  {line}")
        elif line.startswith('@@'):
            print(f"  {line}")
        elif len(line.strip()) > 0:
            print(f"  {line[:70]}{'...' if len(line) > 70 else ''}")
    if len(diff_content.split('\n')) > 10:
        print(f"  ... ({len(diff_content.split('\n')) - 10} more lines)")
    print()
    
    # Initialize and run module finder
    finder = Module_finder()
    
    try:
        hits = finder.find_modules(scala_files, verilog_module, diff_content)
        
        # Filter by confidence threshold
        filtered_hits = [hit for hit in hits if hit.confidence >= args.min_confidence]
        
        # Get base path for relative display
        base_path = os.path.commonpath([args.diff] + scala_files) if scala_files else None
        
        print_results(filtered_hits, base_path, args.verbose)
        
        if len(filtered_hits) != len(hits):
            print(f"\n📊 Total matches found: {len(hits)} (showing {len(filtered_hits)} above threshold)")
        
    except Exception as e:
        print(f"❌ Error during analysis: {e}")
        if args.verbose:
            import traceback
            traceback.print_exc()
        sys.exit(1)


if __name__ == '__main__':
    main()