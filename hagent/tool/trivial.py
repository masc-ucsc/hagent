# See LICENSE file for details

from typing import Optional


class Trivial:
    """
    Trivial example of a tool.
    """

    def __init__(self):
        """
        Initializes the Trivial object
        """
        self.error_message = ''
        self._some_path = '/'

    def setup(self, some_path: Optional[str] = None) -> bool:
        """
        Checks that the tool is installed and ready to use. If not available.
        Returns false, and sets an error_message. Does not raise an exception.

        Returns True if Trivial is ready to use, False otherwise.
        """
        if some_path == '.':
            self.trivial_path_only = True
            self._some_path = '.'
            self.error_message = ''
            return True

        self._some_path = '/'
        self.trivial_path_only = False
        self.error_message = f'Used an invalid setup option: {some_path}'
        return False

    def some_method_related_to_the_tool(self, arg: str) -> str:
        return self._some_private_method(txt=arg)

    def _some_private_method(self, txt: str) -> str:
        return txt + self._some_path
