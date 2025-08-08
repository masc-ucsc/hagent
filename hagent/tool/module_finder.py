import re
from typing import List, Dict, Tuple, Optional
from dataclasses import dataclass
from abc import abstractmethod

from hagent.core.tracer import TracerABCMetaClass


@dataclass
class ModuleHit:
    """Represents a matched module between Verilog and Scala/Chisel"""
    file_name: str
    module_name: str
    start_line: int
    end_line: int
    confidence: float = 1.0  # Confidence score for the match


class Module_finder(metaclass=TracerABCMetaClass):
    """
    Finds Scala/Chisel modules that correspond to Verilog modules in a diff.
    
    Given a list of Scala files, a Verilog module name, and a Verilog diff,
    this class identifies which Scala/Chisel classes likely correspond to 
    the modified Verilog modules.
    """
    
    def __init__(self):
        self.verilog_module_pattern = re.compile(r'^\s*module\s+(\w+)', re.MULTILINE)
        self.scala_class_pattern = re.compile(r'^\s*class\s+(\w+)', re.MULTILINE)
        self.scala_object_pattern = re.compile(r'^\s*object\s+(\w+)', re.MULTILINE)
        self.diff_module_pattern = re.compile(r'@@.*@@.*module\s+(\w+)', re.MULTILINE)
        
    def find_modules(self, scala_files: List[str], verilog_module: str, verilog_diff: str) -> List[ModuleHit]:
        """
        Main method to find corresponding modules.
        
        Args:
            scala_files: List of paths to Scala/Chisel source files
            verilog_module: Name of the primary Verilog module being analyzed
            verilog_diff: The unified diff content containing Verilog changes
            
        Returns:
            List of ModuleHit objects representing potential matches
        """
        hits = []
        
        # Extract module names from the diff
        diff_modules = self._extract_modules_from_diff(verilog_diff)
        
        # If no modules found in diff, use the provided module name
        if not diff_modules:
            diff_modules = [verilog_module] if verilog_module else []
            
        # Search for corresponding Scala/Chisel modules
        for scala_file in scala_files:
            try:
                file_hits = self._find_modules_in_file(scala_file, diff_modules)
                hits.extend(file_hits)
            except (IOError, OSError) as e:
                # Skip files that can't be read
                continue
                
        # Sort hits by confidence score (descending)
        hits.sort(key=lambda x: x.confidence, reverse=True)
        
        return hits
    
    def _extract_modules_from_diff(self, verilog_diff: str) -> List[str]:
        """Extract module names that appear in the diff context"""
        modules = set()
        
        # Look for module declarations in diff context lines
        for line in verilog_diff.split('\n'):
            # Skip diff metadata lines
            if line.startswith('---') or line.startswith('+++') or line.startswith('@@'):
                # Check for module names in @@ context lines
                match = self.diff_module_pattern.search(line)
                if match:
                    modules.add(match.group(1))
                continue
                
            # Look for module declarations in added/removed/context lines
            if line.startswith(('+', '-', ' ')):
                content = line[1:] if line.startswith(('+', '-')) else line
                match = self.verilog_module_pattern.search(content)
                if match:
                    modules.add(match.group(1))
        
        return list(modules)
    
    def _find_modules_in_file(self, scala_file: str, target_modules: List[str]) -> List[ModuleHit]:
        """Find matching modules in a single Scala file"""
        hits = []
        
        try:
            with open(scala_file, 'r', encoding='utf-8') as f:
                content = f.read()
                lines = content.split('\n')
        except (IOError, OSError):
            return hits
            
        # Find all class/object definitions with their line ranges
        scala_modules = self._extract_scala_modules(content, lines)
        
        # Match against target modules
        for target_module in target_modules:
            for scala_module in scala_modules:
                confidence = self._calculate_match_confidence(target_module, scala_module['name'])
                if confidence > 0.3:  # Minimum confidence threshold
                    hit = ModuleHit(
                        file_name=scala_file,
                        module_name=scala_module['name'],
                        start_line=scala_module['start_line'],
                        end_line=scala_module['end_line'],
                        confidence=confidence
                    )
                    hits.append(hit)
        
        return hits
    
    def _extract_scala_modules(self, content: str, lines: List[str]) -> List[Dict]:
        """Extract Scala class/object definitions with line ranges"""
        modules = []
        
        # Find class definitions
        for match in self.scala_class_pattern.finditer(content):
            name = match.group(1)
            start_pos = match.start()
            start_line = content[:start_pos].count('\n') + 1
            end_line = self._find_class_end_line(lines, start_line - 1)  # Convert to 0-based
            
            modules.append({
                'name': name,
                'start_line': start_line,
                'end_line': end_line,
                'type': 'class'
            })
        
        # Find object definitions
        for match in self.scala_object_pattern.finditer(content):
            name = match.group(1)
            start_pos = match.start()
            start_line = content[:start_pos].count('\n') + 1
            end_line = self._find_class_end_line(lines, start_line - 1)  # Convert to 0-based
            
            modules.append({
                'name': name,
                'start_line': start_line,
                'end_line': end_line,
                'type': 'object'
            })
        
        return modules
    
    def _find_class_end_line(self, lines: List[str], start_line_idx: int) -> int:
        """Find the end line of a class/object definition by matching braces"""
        if start_line_idx >= len(lines):
            return start_line_idx + 1
            
        brace_count = 0
        found_opening = False
        
        for i in range(start_line_idx, len(lines)):
            line = lines[i]
            
            # Count braces
            for char in line:
                if char == '{':
                    brace_count += 1
                    found_opening = True
                elif char == '}':
                    brace_count -= 1
                    
            # If we've found the opening brace and returned to balance, we're done
            if found_opening and brace_count == 0:
                return i + 1  # Convert back to 1-based line numbers
                
        # If we couldn't find the end, estimate based on indentation or return a reasonable default
        return min(start_line_idx + 50, len(lines))
    
    def _calculate_match_confidence(self, verilog_name: str, scala_name: str) -> float:
        """Calculate confidence score for a module name match"""
        if not verilog_name or not scala_name:
            return 0.0
            
        # Exact match (case insensitive)
        if verilog_name.lower() == scala_name.lower():
            return 1.0
            
        # Convert names to comparable forms
        v_norm = self._normalize_module_name(verilog_name)
        s_norm = self._normalize_module_name(scala_name)
        
        if v_norm == s_norm:
            return 0.9
            
        # Check for common transformations
        confidence = 0.0
        
        # Check if one contains the other
        if v_norm in s_norm or s_norm in v_norm:
            confidence = max(confidence, 0.8)
            
        # Check for common prefixes/suffixes
        if v_norm.endswith(s_norm) or s_norm.endswith(v_norm):
            confidence = max(confidence, 0.7)
            
        if v_norm.startswith(s_norm) or s_norm.startswith(v_norm):
            confidence = max(confidence, 0.7)
            
        # Levenshtein distance based similarity
        similarity = self._string_similarity(v_norm, s_norm)
        if similarity > 0.6:
            confidence = max(confidence, similarity * 0.6)
            
        return confidence
    
    def _normalize_module_name(self, name: str) -> str:
        """Normalize module names for comparison"""
        # Convert to lowercase and remove underscores
        normalized = name.lower().replace('_', '')
        original_normalized = normalized
        
        # Remove common hardware prefixes/suffixes
        prefixes = ['top', 'module']  # Be more selective with prefixes
        suffixes = ['module', 'unit', 'top']  # Be more selective with suffixes
        
        for prefix in prefixes:
            if normalized.startswith(prefix) and len(normalized) > len(prefix):
                normalized = normalized[len(prefix):]
                
        for suffix in suffixes:
            if normalized.endswith(suffix) and len(normalized) > len(suffix):
                normalized = normalized[:-len(suffix)]
        
        # If normalization resulted in empty string, return the original (minus underscores)
        return normalized if normalized else original_normalized
    
    def _string_similarity(self, s1: str, s2: str) -> float:
        """Calculate string similarity using a simple algorithm"""
        if not s1 and not s2:
            return 1.0  # Both empty strings are identical
            
        if not s1 or not s2:
            return 0.0  # One empty, one not
            
        if s1 == s2:
            return 1.0
            
        # Simple character-based similarity
        max_len = max(len(s1), len(s2))
        if max_len == 0:
            return 1.0
            
        matches = 0
        min_len = min(len(s1), len(s2))
        
        for i in range(min_len):
            if s1[i] == s2[i]:
                matches += 1
                
        return matches / max_len