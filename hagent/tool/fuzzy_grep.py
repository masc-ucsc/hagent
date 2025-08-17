import os
import re
from rapidfuzz import fuzz


class Fuzzy_grep:
    """
    Fuzzy_grep tool class.

    This tool can search a text, a list of files, or all files in a directory for fuzzy matches
    based on provided search terms. The tool can be configured (via setup) with a language
    so that reserved keywords for that language are ignored during matching.
    """

    def __init__(self):
        """
        Initializes the Fuzzy_grep object.
        """
        self.error_message = ''
        self.language = None
        self.reserved_keywords = set()

    def setup(self, language: str = None) -> bool:
        """
        Sets up the tool. If a language is specified, reserved keywords for that language
        are used to filter out fuzzy matches.

        Supported languages: 'verilog', 'scala', 'chisel'. If language is None, no filtering is done.
        Returns True if setup is successful, False otherwise.
        """
        if language is None:
            self.language = None
            self.reserved_keywords = set()
            return True

        language = language.lower()
        if language in ['verilog', 'scala', 'chisel']:
            self.language = language
            self.reserved_keywords = self.get_reserved_keywords(language)
            return True
        else:
            self.error_message = f'Unsupported language: {language}'
            return False

    @staticmethod
    def preprocess(text: str) -> str:
        """
        Remove underscores and digits from the input text and convert to lower-case.
        """
        return re.sub(r'[_\d]', '', text).lower()

    @staticmethod
    def extract_words(text: str) -> list:
        """
        Split text into words based on word characters.
        """
        return re.findall(r'\w+', text)

    @classmethod
    def get_reserved_keywords(cls, language: str) -> set:
        """
        Return a set of preprocessed reserved keywords for the given language.
        Supported languages: 'verilog', 'scala', 'chisel'.
        Returns an empty set if language is not recognized.
        """
        language = language.lower()
        if language == 'verilog':
            keywords = [
                'always',
                'and',
                'assign',
                'begin',
                'buf',
                'case',
                'casex',
                'casez',
                'cmos',
                'deassign',
                'default',
                'defparam',
                'disable',
                'edge',
                'else',
                'end',
                'endcase',
                'endfunction',
                'endmodule',
                'endprimitive',
                'endspecify',
                'endtable',
                'endtask',
                'event',
                'for',
                'force',
                'forever',
                'fork',
                'function',
                'if',
                'initial',
                'inout',
                'input',
                'integer',
                'join',
                'localparam',
                'macromodule',
                'module',
                'nand',
                'negedge',
                'nmos',
                'nor',
                'not',
                'notif',
                'or',
                'output',
                'parameter',
                'pmos',
                'posedge',
                'primitive',
                'pullup',
                'pulsestyle_onevent',
                'pulsestyle_ondetect',
                'rcmos',
                'reg',
                'release',
                'repeat',
                'rnmos',
                'rpmos',
                'rtran',
                'rtranif0',
                'rtranif1',
                'scalared',
                'small',
                'specify',
                'specparam',
                'strength',
                'strong0',
                'strong1',
                'supply0',
                'supply1',
                'table',
                'task',
                'tri',
                'tri0',
                'tri1',
                'triand',
                'trior',
                'trireg',
                'vectored',
                'wait',
                'wand',
                'weak0',
                'weak1',
                'while',
                'wire',
                'wor',
                'xnor',
                'xor',
            ]
        elif language == 'scala':
            keywords = [
                'abstract',
                'case',
                'catch',
                'class',
                'def',
                'do',
                'else',
                'extends',
                'false',
                'final',
                'finally',
                'for',
                'forSome',
                'if',
                'implicit',
                'import',
                'lazy',
                'match',
                'new',
                'null',
                'object',
                'override',
                'package',
                'private',
                'protected',
                'return',
                'sealed',
                'super',
                'this',
                'throw',
                'trait',
                'try',
                'true',
                'type',
                'val',
                'var',
                'while',
                'with',
                'yield',
            ]
        elif language == 'chisel':
            # Combine Scala reserved keywords with additional Chisel-specific keywords.
            scala_keywords = [
                'abstract',
                'case',
                'catch',
                'class',
                'def',
                'do',
                'else',
                'extends',
                'false',
                'final',
                'finally',
                'for',
                'forSome',
                'if',
                'implicit',
                'import',
                'lazy',
                'match',
                'new',
                'null',
                'object',
                'override',
                'package',
                'private',
                'protected',
                'return',
                'sealed',
                'super',
                'this',
                'throw',
                'trait',
                'try',
                'true',
                'type',
                'val',
                'var',
                'while',
                'with',
                'yield',
            ]
            chisel_keywords = [
                'chisel3',
                'module',
                'reg',
                'wire',
                'io',
                'vec',
                'uint',
                'sint',
                'bool',
                'reset',
                'clock',
                'when',
                'otherwise',
                'is',
                'donttouch',
                'rawmodule',
                'blackbox',
                'lazymodule',
                'lazymoduleimp',
                'chiselenum',
                'annotate',
                'input',
                'output',
            ]
            keywords = scala_keywords + chisel_keywords
        else:
            keywords = []
        # Preprocess each keyword for consistent comparison.
        return {cls.preprocess(word) for word in keywords}

    def line_matches(self, line: str, search_terms: list, threshold: int) -> bool:
        """
        Returns True if for every search term, at least one non-reserved (if configured)
        preprocessed word in the line has a fuzzy match with the preprocessed search term
        with a score at or above the threshold.
        """

        # Skip processing if the line is a comment.
        if re.match(r'^\s*(//|/\*|\*)', line):
            return False
        words = self.extract_words(line)
        # Filter out reserved words.
        candidate_words = [
            self.preprocess(word)
            for word in words
            if not (self.reserved_keywords and self.preprocess(word) in self.reserved_keywords)
        ]
        for term in search_terms:
            proc_term = self.preprocess(term)

            if any(fuzz.ratio(proc_term, candidate) >= threshold for candidate in candidate_words):
                return True
        return False

    def find_matches_in_text(self, text: str, search_terms: list, threshold: int) -> list:
        """
        Searches the given text and returns a list of tuples (line_number, line_content)
        for lines that match all search terms.
        """
        lines = text.splitlines()
        indices = list()
        for i, line in enumerate(lines):
            if self.line_matches(line, search_terms, threshold):
                indices.append(i)

        return [(i, lines[i].rstrip('\n')) for i in indices]

    def find_matches_in_file(self, file_path: str, search_terms: list, threshold: int) -> list:
        """
        Reads the file and returns a list of tuples (line_number, line_content)
        for lines that match all search terms.
        """
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                text = f.read()
            return self.find_matches_in_text(text, search_terms, threshold)
        except Exception as e:
            self.error_message = str(e)
            return []

    def search(
        self,
        text: str = None,
        files: list = None,
        directory: str = None,
        search_terms: list = None,
        threshold: int = 70,
    ) -> dict:
        """
        Searches for fuzzy matches based on search_terms.

        Provide one of the following inputs:
          - text: a string to search.
          - files: a list of file paths.
          - directory: a directory whose files (non-recursively) are to be searched.

        Returns a dictionary with keys being either "text" or file paths, and values as a list of
        (line_number, line_content) tuples.
        """
        results = {}
        if text is not None:
            results['text'] = self.find_matches_in_text(text, search_terms, threshold)
        if files is not None:
            for file in files:
                if os.path.isfile(file):
                    matches = self.find_matches_in_file(file, search_terms, threshold)
                    if matches:
                        results[file] = matches
                else:
                    results[file] = []  # File not found or invalid.
        if directory is not None:
            if os.path.isdir(directory):
                for entry in os.listdir(directory):
                    file_path = os.path.join(directory, entry)
                    if os.path.isfile(file_path):
                        matches = self.find_matches_in_file(file_path, search_terms, threshold)
                        if matches:
                            results[file_path] = matches
            else:
                self.error_message = f'{directory} is not a valid directory.'
        return results
