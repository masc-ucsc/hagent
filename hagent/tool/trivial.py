# See LICENSE for details

from typing import Optional
from hagent.tool.tool import Tool


class Trivial(Tool):
    """
    Trivial example of a tool using the Tool class.
    """

    def __init__(self):
        """
        Initializes the Trivial object
        """
        super().__init__()
        self._some_path = '/'
        self.trivial_path_only = False

    def setup(self, some_path: Optional[str] = None) -> bool:
        """
        Checks that the tool is installed and ready to use.

        Args:
            some_path: Path to use for the tool

        Returns:
            True if Trivial is ready to use, False otherwise.
        """
        if some_path == '.':
            self._some_path = '.'
            self.trivial_path_only = True
            self._is_ready = True
            self.error_message = ''
            return True

        self._some_path = '/'
        self.trivial_path_only = False
        self.set_error(f'Used an invalid setup option: {some_path}')
        return False

    def some_method_related_to_the_tool(self, arg: str) -> str:
        """
        Example method that demonstrates tool functionality.

        Args:
            arg: Input string

        Returns:
            Processed string
        """
        return self._some_private_method(txt=arg)

    def _some_private_method(self, txt: str) -> str:
        """
        Private helper method.

        Args:
            txt: Input string

        Returns:
            String with path appended
        """
        return txt + self._some_path
