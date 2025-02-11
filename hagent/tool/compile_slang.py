from typing import Optional, List
from collections import namedtuple

try:
    import pyslang
except ImportError:
    pyslang = None  # type: ignore

Diagnostic = namedtuple('Diagnostic', ['msg', 'loc', 'hint'])
IO = namedtuple('IO', ['name', 'input', 'output', 'bits'])


class Compile_slang:
    """
    A HAgent tool pyslang (slang) wrapper to compile and extract information from Verilog.
    """

    # Attributes:
    #   error_message (str): Holds the last error message (empty if no error).
    #   _compiler (pyslang.Compilation): Slang compiler base object with all the source
    def __init__(self):
        """
        Initializes the SlangTool instance with a new pyslang.Compilation object,
        an empty error message
        """
        self.error_message = ''
        self._compiler = None
        self._top_module = None

    def setup(self) -> bool:
        """
        Validates the presence of the pyslang package.
        Does not raise exceptions; returns True if setup is successful, False otherwise.
        Updates error_message on failure.
        Initializes self._compiler with these options:
            copt = pyslang.CompilationOptions()
            copt.errorLimit = 1
            copt.flags = pyslang.CompilationFlags.IgnoreUnknownModules
        Returns:
            bool: True if setup is successful, False otherwise.
        """
        if pyslang is None:
            self.error_message = 'pyslang package not found. Please install it.'
            return False

        try:
            copt = pyslang.CompilationOptions()
            copt.errorLimit = 1
            copt.flags = pyslang.CompilationFlags.IgnoreUnknownModules
            self._compiler = pyslang.Compilation(pyslang.Bag([copt]))

        except Exception as e:
            self.error_message = f'Failed to initialize pyslang.Compilation: {e}'
            return False

        self.error_message = ''  # Reset in case of previous errors.
        return True

    def add_source(self, text: Optional[str] = None, file: Optional[str] = None) -> bool:
        """
        Either text or file must be provided.
        Depending on the input type, uses pyslang.SyntaxTree.fromText or pyslang.SyntaxTree.fromFile.
        Parameters:
            text (str): The input string
            file (str): The input file to use
        Returns:
            The source included may have compile errors, the error_message is
            only updated if the file did not exist or an exception is raised by
            slang.
        """
        if not pyslang or not self._compiler:
            return False

        if text is None and file is None:
            self.error_message = "Either 'text' or 'file' must be provided."
            return False
        if text is not None and file is not None:
            self.error_message = "Only one of 'text' or 'file' should be provided."
            return False

        try:
            if text:
                tree = pyslang.SyntaxTree.fromText(text)
            else:
                tree = pyslang.SyntaxTree.fromFile(file)
            self._compiler.addSyntaxTree(tree)

        except FileNotFoundError:
            self.error_message = f'File not found: {file}'
            return False
        except Exception as e:
            self.error_message = f'Error adding source: {e}'
            return False
        return True

    def set_top(self, top: str) -> bool:
        """
        Using the currently compiled files, set the top. If it does not exist, it returns false, but no error_message is set.
        Returns:
            True if the top exist in the compile (previously add_source) source. False otherwise.
        """
        if self._compiler is None:
            return False

        definition = self._compiler.getRoot().lookupName(top)
        if definition:
            self._top_module = top
            return True
        return False

    def get_top(self) -> str:
        if not self._compiler:
            return ''

        if not self._top_module:
            inst = self._compiler.getRoot().topInstances
            if len(inst) != 1:
                self.error_message = 'uname to find a single top module'
                return ''
            top = str(inst[0].name)
        else:
            top = self._top_module

        return top

    def get_hierarchy(self, modname: str = "") -> List[str]:
        """
        Extracts and returns a list of hierarchical names or identifiers by traversing
        the top-level instances in the compilation root.
        Returns:
            List[str]: A list of module or instance names representing the hierarchy.
        """
        if not self._compiler:
            return []

        if self._top_module:
            if self._top_module == modname or not modname:
                return [self._top_module]

        if not modname:
            inst = self._compiler.getRoot().topInstances
            return [i.name for i in inst]

        top = modname

        definition = self._compiler.getRoot().lookupName(top)
        if not definition:
            return []

        return [top]

    def get_ios(self, modname: str = None) -> List[IO]:
        """
        Extracts input/output definitions from the specified modname. If no module name is provided, the "top" is used.
        It looks up the module by name and iterates through its body to extract port information (e.g., direction,
        fixed range, name).
        Parameters:
            modname (str): The name of the module to extract IO information from.
        Returns:
            List[IO]: A list of IOs, Each entry has a named struct "name:str, input:bool, output:bool, bits:int".
        """
        ios = []
        if not self._compiler:
            return []

        if not modname:
            modname = self.get_top()

        definition = self._compiler.getRoot().lookupName(modname)
        if not definition:
            return []  # Module not found.

        try:
            for stmt in definition.body:
                if stmt.kind == pyslang.SymbolKind.Port:
                    if stmt.direction == pyslang.ArgumentDirection.In:
                        input_dir = True
                        output_dir = False
                    elif stmt.direction == pyslang.ArgumentDirection.Out:
                        input_dir = False
                        output_dir = True
                    else:
                        input_dir = True
                        output_dir = True

                    bits = stmt.type.bitWidth
                    ios.append(IO(name=stmt.name, input=input_dir, output=output_dir, bits=bits))

        except AttributeError:  # pragma: no cover #  pyslang internals, hard to test all corner cases.
            return []
        return ios

    def get_warnings(self) -> List[Diagnostic]:
        """
        Retrieves and returns a list of formatted warning messages from the compilation diagnostics.
        The returned List is a named struct with these fields:
          msg: txt -- a single line complies with the gcc/clang error/warning format. E.g:
            source:5:12: warning: implicit conversion truncates from 3 to 2 bits [-Wwidth-trunc]
          loc: int -- the line of code (5) in the previous example
          hint: txt -- The optional hint or more detailed multiline message. E.g:
            assign c = a ^ tmp;
                    ~ ^~~~~~~
        Returns:
            List[Diagnostic]: A list of warning messages.
        """
        if not pyslang:
            return []

        return self._get_diagnostics(errors=False)

    def get_errors(self) -> List[Diagnostic]:
        """
        Retrieves and returns a list of formatted error messages from the compilation diagnostics.
        The format is the same as the get_warnings
        Returns:
            List[Diagnostic]: A list of error messages.
        """
        if not pyslang:
            return []

        return self._get_diagnostics(errors=True)

    def _parse_error_message(self, error_str: str) -> Diagnostic:
        parts = error_str.split('\n', 1)
        main_msg = parts[0]
        hint = parts[1] if len(parts) > 1 else ''

        msg_parts = main_msg.split(':')
        loc = int(msg_parts[1])

        msg = msg_parts[-1].strip()
        if 'error:' in main_msg:
            msg = main_msg.split('error:')[-1].strip()
        elif 'warning:' in main_msg:
            msg = main_msg.split('error:')[-1].strip()

        return Diagnostic(msg=msg, loc=loc, hint=hint)

    def _get_diagnostics(self, errors: bool) -> List[Diagnostic]:
        """Helper function to retrieve and format diagnostics."""
        if not self._compiler or not pyslang:
            return []

        diagnostics = []

        diags = self._compiler.getAllDiagnostics()
        deng = pyslang.DiagnosticEngine(self._compiler.sourceManager)
        for msg in diags:
            if msg.isError() == errors:
                txt = deng.reportAll(self._compiler.sourceManager, [msg])
                diagnostics.append(self._parse_error_message(txt))

        return diagnostics
