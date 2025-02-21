from typing import Optional, List
from collections import namedtuple

try:
    import pyslang
except ImportError:
    pyslang = None  # type: ignore

from hagent.tool.compile import Diagnostic

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

    def setup(self, args: Optional[str] = '') -> bool:
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
        if not pyslang:
            return False

        try:
            # Create a slang driver with default command line arguments
            driver = pyslang.Driver()
            driver.addStandardArgs()

            # Parse command line arguments
            if not driver.parseCommandLine(f'slang --ignore-unknown-modules {args}', pyslang.CommandLineOptions()):
                return False

            if args:
                if not driver.processOptions():
                    self.error_message = f'could not process slang options: {args}'
                    return False

                if not driver.parseAllSources():
                    self.error_message = f'count not process slang source files: {args}'
                    return False

            compilation = driver.createCompilation()

            self._sm = driver.sourceManager
            self._compiler = compilation

            # tree = pyslang.SyntaxTree.fromFile("trivial.v", self._sm)
            # compilation.addSyntaxTree(tree)
            # inst = compilation.getRoot().topInstances
            # for i in inst:
            #     print(f"OTATO:{i}")
        except Exception as e:
            self.error_message = f'could not process add_file {args}: {e}'
            return False

        return True

    def add_inline(self, text: str) -> bool:
        """
        Parameters:
            text (str): The input string
        Returns:
            The source included may have compile errors, the error_message is
            only updated if the file did not exist or an exception is raised by
            slang.
        """
        if not pyslang or not self._compiler:
            return False

        try:
            tree = pyslang.SyntaxTree.fromText(text=text, sourceManager=self._sm, name='inline')
            self._compiler.addSyntaxTree(tree)

        except Exception as e:
            self.error_message = f'Error adding source: {e}'
            return False

        return True

    def add_file(self, file: str) -> bool:
        """
        Parameters:
            file (str): The input file to use
        Returns:
            The source included may have compile errors, the error_message is
            only updated if the file did not exist or an exception is raised by
            slang.
        """
        if not pyslang or not self._compiler:
            return False

        try:
            if not self._sm:
                self._sm = self._compiler.sourceManager
            tree = pyslang.SyntaxTree.fromFile(file, sourceManager=self._sm)
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

    def get_top_list(self, modname: str = '') -> List[str]:
        """
        Extracts and returns a list of top modules names or identifiers by traversing
        the top-level instances in the compilation root.
        Returns:
            List[str]: A list of module or instance names representing the top module list.
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

    def _get_diagnostics(self, errors: bool) -> List[Diagnostic]:
        """Helper function to retrieve and format diagnostics."""
        if not self._compiler or not pyslang:
            return []

        diagnostics = []

        diags = self._compiler.getAllDiagnostics()
        deng = pyslang.DiagnosticEngine(self._sm)
        for msg in diags:
            if msg.isError() == errors:
                txt = deng.reportAll(self._sm, [msg])
                diagnostics.append(Diagnostic(txt))

        return diagnostics
