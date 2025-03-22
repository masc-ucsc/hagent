
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

    #print(formatted_code)


# Run the example if this file is executed directly
if __name__ == '__main__':
    test_example()
