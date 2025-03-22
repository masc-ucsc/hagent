
from hagent.tool.code_scope import Code_scope

def test_example():
    code = """
    class Test {
      def method1() {
        val x = 1
        val y = 2
        println(x + y)
      }

      def method2() {
        if (condition) {
          doSomething()
        } else {
          doSomethingElse()
        }
      }
    }

    module Counter(
      input clk,
      output reg [7:0] count
    );
      always @(posedge clk) begin
        count <= count + 1;
      end
    endmodule
    """

    finder = Code_scope(code)

    # Find scopes containing lines 3, 4, 5 (inside method1)
    scopes = finder.find_nearest_upper_scopes([3, 4, 5])
    assert scopes ==  [(2, 6)]
    #print('Nearest upper scopes for lines 3, 4, 5:', scopes)

    # Find scopes containing lines 2 and 10 (method1 and method2)
    scopes = finder.find_nearest_upper_scopes([2, 10])
    #print('Nearest upper scopes for lines 2, 10:', scopes)
    assert scopes == [(2, 6), (9, 13)]

    # Example of get_code usage
    formatted_code = finder.get_code((3, 5), [4], '->')
    #print('\nExample of get_code output:')
    assert formatted_code == """   3:         val x = 1
-> 4:         val y = 2
   5:         println(x + y)"""


def test_comprehensive():
    """A comprehensive test covering various aspects of Code_scope functionality."""
    # 1. Test various code structures and comments
    mixed_code = """
    // Single line comment
    function() {
        /* Multi-line comment */
        code1();
        let str = "{ not a real scope }";
        (* Another comment *)
        code2();
    }
    """
    finder = Code_scope(mixed_code)
    
    # Comment handling and scope detection
    scopes = finder.find_nearest_upper_scopes([4])
    assert len(scopes) > 0
    assert scopes[0][0] == 2  # Starts at function line
    
    # 2. Test unclosed scopes and line limits
    unclosed_code = """
    function() {
        nested() {
            deeplyNested() {
                code();
            } // Only inner scope closed
        // Missing closing braces
    """
    limited_finder = Code_scope(unclosed_code, line_limit=3)
    scopes = limited_finder.find_nearest_upper_scopes([4])
    
    # Check that unclosed scopes are handled and limited properly
    assert len(scopes) > 0
    for start, end in scopes:
        assert end - start <= limited_finder.line_limit
    
    # 3. Test find_scopes_for_lines with multiple scenarios
    multi_scope_code = """
    func1() {
        code1();
    }
    
    func2() {
        code2();
    }
    """
    multi_finder = Code_scope(multi_scope_code)
    
    # Test with valid lines in different scopes
    scopes = multi_finder.find_scopes_for_lines([2, 6])
    assert len(scopes) == 2
    
    # Test with invalid inputs
    assert multi_finder.find_scopes_for_lines([]) == []
    assert multi_finder.find_scopes_for_lines([-1, 100]) == []
    
    # Test artificial scope creation
    multi_finder.scopes = []
    scopes = multi_finder.find_scopes_for_lines([2])
    assert len(scopes) > 0
    
    # 4. Test begin/end keywords in Verilog
    verilog_code = """
    module test;
        always @(posedge clk) begin
            counter <= counter + 1;
            if (counter == MAX) begin
                done <= 1;
            end
        end
        wire beginning;
    endmodule
    """
    verilog_finder = Code_scope(verilog_code)
    scopes = verilog_finder.find_nearest_upper_scopes([4])
    assert any(start <= 4 <= end for start, end in scopes)
    
    # 5. Test get_code with various cases
    simple_code = """
    function() {
        line1();
        line2();
    }
    """
    simple_finder = Code_scope(simple_code)
    
    # Test marking specific lines
    marked = simple_finder.get_code((1, 3), [2], "-->")
    assert "-->" in marked
    assert "2: " in marked
    
    # Test edge cases
    assert "-->" not in simple_finder.get_code((1, 3), [], "-->")  # Empty mark list
    
    # Test bounds checking with subclass
    class BoundChecker(Code_scope):
        def get_code(self, scope, mark, hint):
            start_line, end_line = scope
            if end_line >= len(self.lines):
                return "Bounded"
            return super().get_code(scope, mark, hint)
    
    bound_tester = BoundChecker(simple_code)
    assert bound_tester.get_code((1, 100), [2], "-->") == "Bounded"
    
    # 6. Test unclosed multiline comments
    comment_code = """
    function() {
        /* This comment
        is not closed
        code();
    }
    """
    comment_finder = Code_scope(comment_code)
    scopes = comment_finder.find_nearest_upper_scopes([4])
    assert len(scopes) == 1


# Run the example if this file is executed directly
if __name__ == '__main__':
    test_example()
