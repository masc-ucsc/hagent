import unittest
from hagent.tool.compile import Diagnostic


class test_diagnostics(unittest.TestCase):
    def test_diagnostic_error(self):
        error_str = "src/main.c:12: error: 'x' undeclared (first use in this function)"
        diag = Diagnostic(error_str)
        self.assertEqual(diag.file, 'src/main.c')
        self.assertEqual(diag.loc, 12)
        self.assertEqual(diag.msg, "'x' undeclared (first use in this function)")
        self.assertEqual(diag.hint, '')

    def test_diagnostic_warning(self):
        warning_str = "src/main.c:20: warning: implicit declaration of function 'y'"
        diag = Diagnostic(warning_str)
        self.assertEqual(diag.file, 'src/main.c')
        self.assertEqual(diag.loc, 20)
        self.assertEqual(diag.msg, "implicit declaration of function 'y'")
        self.assertEqual(diag.hint, '')

    def test_diagnostic_no_location(self):
        error_str = 'some error message without location'
        diag = Diagnostic(error_str)
        self.assertEqual(diag.file, '')
        self.assertEqual(diag.loc, -1)
        self.assertEqual(diag.msg, 'some error message without location')
        self.assertEqual(diag.hint, '')

    def test_diagnostic_with_hint(self):
        error_str = "src/main.c:12: error: 'x' undeclared\nDid you mean 'y'?"
        diag = Diagnostic(error_str)
        self.assertEqual(diag.file, 'src/main.c')
        self.assertEqual(diag.loc, 12)
        self.assertEqual(diag.msg, "'x' undeclared")
        self.assertEqual(diag.hint, "Did you mean 'y'?")

    def test_insert_comment(self):
        code = """int main() {\n    int x;\n    return 0;\n}\n"""
        error_str = "src/main.c:2: error: 'x' undeclared"
        diag = Diagnostic(error_str)

        commented_code = diag.insert_comment(code, '//')
        expected_code = """int main() {\n// FIXME_HINT: 'x' undeclared\n    int x;\n    return 0;\n}\n"""
        self.assertEqual(commented_code, expected_code)

    def test_remove_comment(self):
        code = """int main() {\n// FIXME_HINT: 'x' undeclared\n    int x;\n    return 0;\n}\n"""
        error_str = "src/main.c:2: error: 'x' undeclared"
        diag = Diagnostic(error_str)

        cleaned_code = diag.remove_comment(code, '//')
        expected_code = """int main() {\n    int x;\n    return 0;\n}\n"""
        self.assertEqual(cleaned_code, expected_code)


if __name__ == '__main__':
    unittest.main()
