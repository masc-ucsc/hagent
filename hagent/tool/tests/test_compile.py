import unittest

from hagent.tool.compile import Diagnostic


class test_diagnostics(unittest.TestCase):
    def test_diagnostic_error(self):
        error_str = "src/main.c:12: error: 'x' undeclared (first use in this function)"
        diag = Diagnostic(error_str)
        self.assertEqual(diag.loc, 12)
        self.assertEqual(diag.msg, "'x' undeclared (first use in this function)")
        self.assertEqual(diag.hint, '')

    def test_diagnostic_warning(self):
        warning_str = "src/main.c:20: warning: implicit declaration of function 'y'"
        diag = Diagnostic(warning_str)
        self.assertEqual(diag.loc, 20)
        self.assertEqual(diag.msg, "implicit declaration of function 'y'")
        self.assertEqual(diag.hint, '')

    def test_diagnostic_no_location(self):
        error_str = 'some error message without location'
        diag = Diagnostic(error_str)
        self.assertIsNone(diag.loc)
        self.assertEqual(diag.msg, 'some error message without location')
        self.assertEqual(diag.hint, '')

    def test_diagnostic_with_hint(self):
        error_str = "src/main.c:12: error: 'x' undeclared\nDid you mean 'y'?"
        diag = Diagnostic(error_str)
        self.assertEqual(diag.loc, 12)
        self.assertEqual(diag.msg, "'x' undeclared")
        self.assertEqual(diag.hint, "Did you mean 'y'?")


if __name__ == '__main__':
    unittest.main()
