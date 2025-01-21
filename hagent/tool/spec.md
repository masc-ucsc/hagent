
## Hagent tools

This directory contains either subdirectories or a single Python file for each Tool support in HAgent.

A sample of tool is trivial.py
```
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
            return True

        self._some_path = '/'
        self.trivial_path_only = False
        self.error_message = f'Used an invalid setup option: {some_path}'
        return False

    def some_method_related_to_the_tool(self, arg: str):
        self._some_private_method(arg)

    def _some_private_method(self, txt: str):
        return txt + self._some_path
```

Some common characteristics for all the tools:
* a `setup` method that returns True/False depending on the setup and depencences. It should be called only once per execution.
* `error_message` containts either an empty string or the error message from the last call.
* List of custom methods per tool.
* The setup does not raise exceptions, but failures in the custom methods raise `RuntimeError` exceptions.
* Each file should have a corresponding unit test checking the API.

An example of Trivial.py test in the `tests/test_trivial.py` file.
```
# See LICENSE file for details

import pytest
from hagent.tool.trivial import Trivial


def test_used_dot():
    dut = Trivial()

    assert dut.error_message == ''
    assert dut.some_method_related_to_the_tool('xx') == 'xx/'

    dut.setup('potato')
    assert dut.some_method_related_to_the_tool('xx') == 'xx/'
    assert dut.error_message != ''

    dut.setup('.')
    assert dut.some_method_related_to_the_tool('xx') == 'xx.'
    assert dut.error_message == ''


if __name__ == '__main__':  # pragma: no cover
    test_used_dot()
```

