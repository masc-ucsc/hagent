#!/usr/bin/env python3
"""
Simple Hints Generator Test - Easy to use version

Just run this, paste your diff, then press Enter twice to get hints!

Usage:
    uv run python hagent/step/v2chisel_batch/tests/simple_hints_test.py
"""

import os
import sys
import tempfile
from pathlib import Path
from unittest.mock import Mock
from types import SimpleNamespace

# Set environment before importing
os.environ['HAGENT_EXECUTION_MODE'] = 'docker'

# Add project root to path  
sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent.parent))

from hagent.step.v2chisel_batch.components.hints_generator import HintsGenerator
from hagent.step.v2chisel_batch.components.bug_info import BugInfo


def create_mock_chisel_files():
    """Create realistic Chisel files for testing"""
    
    control_content = '''package dinocpu.components

import chisel3._
import chisel3.util.{BitPat, ListLookup}

class Control extends Module {
  val io = IO(new Bundle {
    val opcode = Input(UInt(7.W))
    val itype = Output(Bool())
    val aluop = Output(Bool())
    val regwrite = Output(Bool())
    val validinst = Output(Bool())
    val wordinst = Output(Bool())
  })

  val signals = ListLookup(io.opcode,
    List(false.B, false.B, false.B, false.B, false.B),
    Array(
      BitPat("b0110011") -> List(false.B,  true.B,   true.B,    true.B,  false.B),
      BitPat("b0010011") -> List( true.B,  true.B,   true.B,    true.B,  false.B),
      BitPat("b0000011") -> List(false.B, false.B,   true.B,    true.B,  false.B),
      BitPat("b0111011") -> List(false.B,  true.B,   true.B,    true.B,   true.B),
    ))

  io.itype := signals(0)
  io.aluop := signals(1)
  io.regwrite := signals(2)
  io.validinst := signals(3)
  io.wordinst := signals(4)
}'''
    
    alu_content = '''package dinocpu.components

import chisel3._
import chisel3.util._

class ALU extends Module {
  val io = IO(new Bundle {
    val operation = Input(UInt(4.W))
    val inputx = Input(UInt(64.W))
    val inputy = Input(UInt(64.W))
    val result = Output(UInt(64.W))
  })

  switch (io.operation) {
    is (0.U) { io.result := io.inputx & io.inputy }
    is (1.U) { io.result := io.inputx | io.inputy }
    is (2.U) { io.result := io.inputx + io.inputy }
    is (6.U) { io.result := io.inputx - io.inputy }
    is (7.U) { io.result := io.inputx < io.inputy }
  }
}'''
    
    temp_files = []
    for name, content in [('Control.scala', control_content), ('ALU.scala', alu_content)]:
        temp_fd, temp_path = tempfile.mkstemp(suffix='.scala', prefix=f'{name[:-6]}_')
        with os.fdopen(temp_fd, 'w') as f:
            f.write(content)
        temp_files.append(temp_path)
    
    return temp_files


def create_mock_module_finder(chisel_files, module_name):
    """Create a mock module_finder that returns hits"""
    mock_module_finder = Mock()
    
    mock_hits = []
    for file_path in chisel_files:
        if module_name.lower() in file_path.lower() or 'Control' in file_path:
            mock_hit = SimpleNamespace()
            mock_hit.file_name = file_path
            mock_hit.module_name = module_name
            mock_hit.start_line = 15
            mock_hit.end_line = 25
            mock_hit.confidence = 0.9
            mock_hits.append(mock_hit)
            break
    
    if not mock_hits and chisel_files:
        mock_hit = SimpleNamespace()
        mock_hit.file_name = chisel_files[0]
        mock_hit.module_name = module_name
        mock_hit.start_line = 10
        mock_hit.end_line = 20
        mock_hit.confidence = 0.7
        mock_hits.append(mock_hit)
    
    mock_module_finder.find_modules.return_value = mock_hits
    return mock_module_finder


def get_diff_from_user():
    """Get diff from user - simple method with double enter"""
    print("🎯 SIMPLE HINTS GENERATOR")
    print("=" * 40)
    print("Paste your Verilog diff below, then press Enter TWICE when done:")
    print()
    
    lines = []
    empty_lines = 0
    
    while True:
        try:
            line = input()
            if line == "":
                empty_lines += 1
                if empty_lines >= 2:
                    break
            else:
                empty_lines = 0
                lines.append(line)
        except (EOFError, KeyboardInterrupt):
            break
    
    return '\n'.join(lines)


def find_docker_chisel_files(container_name):
    """Find Chisel files in Docker container"""
    import subprocess
    
    print(f"🔍 Searching for Chisel files in Docker container '{container_name}'...")
    
    try:
        # Search for .scala files in the container
        cmd = ['docker', 'exec', container_name, 'find', '/code/workspace', '-name', '*.scala', '-type', 'f']
        result = subprocess.run(cmd, capture_output=True, text=True, check=True)
        
        scala_files = [f"docker:{container_name}:{line.strip()}" 
                      for line in result.stdout.strip().split('\n') 
                      if line.strip() and '/code/workspace' in line]
        
        print(f"✅ Found {len(scala_files)} Chisel files in container")
        for f in scala_files[:5]:  # Show first 5
            file_path = f.split(':', 2)[2]
            print(f"   📁 {file_path}")
        if len(scala_files) > 5:
            print(f"   ... and {len(scala_files) - 5} more")
            
        return scala_files
        
    except subprocess.CalledProcessError as e:
        print(f"❌ Failed to find files in container: {e}")
        return []
    except Exception as e:
        print(f"❌ Error accessing container: {e}")
        return []


def get_container_name():
    """Get Docker container name from user"""
    print("🐳 DOCKER CONTAINER SETUP")
    print("-" * 30)
    print("To search real Chisel files, I need your Docker container name.")
    print()
    
    # Try to list running containers
    try:
        import subprocess
        result = subprocess.run(['docker', 'ps', '--format', 'table {{.Names}}\t{{.Image}}'], 
                              capture_output=True, text=True)
        if result.returncode == 0 and result.stdout:
            lines = result.stdout.strip().split('\n')
            if len(lines) > 1:  # Has header + containers
                print("Running containers:")
                for line in lines:
                    print(f"  {line}")
                print()
    except:
        pass
    
    container = input("Enter your Docker container name (or press Enter to use mock files): ").strip()
    return container if container else None


def main():
    print("Welcome! This tool takes your Verilog diff and shows you Chisel hints.")
    print()
    
    # Get container name first
    container_name = get_container_name()
    use_docker = container_name is not None
    
    # Get diff from user
    diff = get_diff_from_user()
    
    if not diff.strip():
        print("❌ No diff provided!")
        return
    
    print(f"\n✅ Got diff ({len(diff)} characters)")
    print("🔄 Processing...")
    
    try:
        # Parse module name from diff
        lines = diff.split('\n')
        module_file = 'Unknown.sv'
        for line in lines:
            if line.startswith('--- a/') or line.startswith('+++ b/'):
                potential_file = line.split('/')[-1]
                if potential_file.endswith('.sv') or potential_file.endswith('.v'):
                    module_file = potential_file
                    break
        
        module_name = os.path.splitext(module_file)[0]
        
        # Create bug info
        bug_data = {'file': module_file, 'unified_diff': diff}
        bug_info = BugInfo(bug_data, 0)
        
        if use_docker:
            print(f"\n🐳 Using Docker container: {container_name}")
            
            # Find real Chisel files in Docker
            docker_files = find_docker_chisel_files(container_name)
            
            if not docker_files:
                print("⚠️  No Chisel files found in container. Using mock files instead.")
                docker_files = create_mock_chisel_files()
                container_name = 'test_container'
            
            # Use real Module_finder
            try:
                from hagent.tool.module_finder import Module_finder
                real_module_finder = Module_finder()
                hints_gen = HintsGenerator(real_module_finder, debug=True)
                print("✅ Using real Module_finder with Docker files")
            except Exception as e:
                print(f"⚠️  Failed to create real Module_finder: {e}")
                print("🔄 Falling back to mock module_finder...")
                mock_module_finder = create_mock_module_finder(docker_files, module_name)
                hints_gen = HintsGenerator(mock_module_finder, debug=True)
            
            chisel_files = docker_files
            
        else:
            print("🧪 Using mock files for testing")
            # Create test files and mock module finder
            temp_files = create_mock_chisel_files()
            mock_module_finder = create_mock_module_finder(temp_files, module_name)
            hints_gen = HintsGenerator(mock_module_finder, debug=False)
            chisel_files = temp_files
            container_name = 'test_container'
        
        # Generate hints
        print(f"\n🚀 Generating hints for {module_name}...")
        result = hints_gen.find_hints(bug_info, chisel_files, container_name)
        
        # Show results
        print(f"\n🎯 RESULTS for {module_name}")
        print("=" * 50)
        print(f"Success: {result['success']}")
        print(f"Source: {result['source']}")
        print(f"Hits: {len(result['hits'])}")
        
        if result['hits']:
            for i, hit in enumerate(result['hits']):
                file_display = hit.file_name
                if file_display.startswith('docker:'):
                    file_display = hit.file_name.split(':', 2)[2]
                print(f"  Hit {i+1}: {hit.module_name} in {file_display} (confidence: {hit.confidence:.2f})")
        
        print(f"\n📝 CHISEL HINTS:")
        print("-" * 50)
        print(result['hints'])
        
        if result['success']:
            print("✅ Found hints! Look at the Chisel code above.")
            if use_docker:
                print(f"💡 The hints point to real files in your Docker container '{container_name}'")
        else:
            print("❌ No specific hints found, but that's normal for some diffs.")
            
        # Cleanup temp files (only if using mock)
        if not use_docker:
            for temp_file in chisel_files:
                try:
                    os.unlink(temp_file)
                except:
                    pass
                
    except Exception as e:
        print(f"❌ Error: {e}")


if __name__ == '__main__':
    main()