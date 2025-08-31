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

        commented_code = diag._insert_comment(code, '//')
        expected_code = """int main() {\n// FIXME_HINT: 'x' undeclared\n    int x;\n    return 0;\n}\n"""
        self.assertEqual(commented_code, expected_code)

    def test_remove_comment(self):
        code = """int main() {\n// FIXME_HINT: 'x' undeclared\n    int x;\n    return 0;\n}\n"""
        error_str = "src/main.c:2: error: 'x' undeclared"
        diag = Diagnostic(error_str)

        cleaned_code = diag._remove_comment(code, '//')
        expected_code = """int main() {\n    int x;\n    return 0;\n}\n"""
        self.assertEqual(cleaned_code, expected_code)

    def test_insert_comment_invalid_line(self):
        """Test insert_comment with an invalid line number."""
        code = """int main() {\n    int x;\n    return 0;\n}\n"""
        error_str = "src/main.c:10: error: 'x' undeclared"
        diag = Diagnostic(error_str)

        # Test with a line number that is out of range
        with self.assertRaises(ValueError):
            diag._insert_comment(code, '//')

        # Test with a negative line number
        diag.loc = -5
        with self.assertRaises(ValueError):
            diag._insert_comment(code, '//')

    def test_to_str_error(self):
        """Test to_str method with an error diagnostic."""
        error_str = "src/main.c:12: error: 'x' undeclared"
        diag = Diagnostic(error_str)
        diag.error = True

        result = diag.to_str()

        self.assertIn('File src/main.c Line 12 has an error stating:', result)
        self.assertIn("'x' undeclared", result)
        self.assertNotIn('Possible hint:', result)

    def test_to_str_warning(self):
        """Test to_str method with a warning diagnostic."""
        warning_str = "src/main.c:20: warning: implicit declaration of function 'y'"
        diag = Diagnostic(warning_str)
        diag.error = False

        result = diag.to_str()

        self.assertIn('File src/main.c Line 20 has an warning stating:', result)
        self.assertIn("implicit declaration of function 'y'", result)
        self.assertNotIn('Possible hint:', result)

    def test_to_str_with_hint(self):
        """Test to_str method with a diagnostic that has a hint."""
        error_str = "src/main.c:12: error: 'x' undeclared\nDid you mean 'y'?"
        diag = Diagnostic(error_str)

        result = diag.to_str()

        self.assertIn('File src/main.c Line 12 has', result)
        self.assertIn("'x' undeclared", result)
        self.assertIn('Possible hint:', result)
        self.assertIn("Did you mean 'y'?", result)


if __name__ == '__main__':
    unittest.main()
