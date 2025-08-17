// Implementation with incorrect behavior
module add_impl(
    input [7:0] a,
    input [7:0] b,
    output [8:0] sum
);
    // Incorrect: subtracts instead of adds
    assign sum = a - b;
endmodule

module mult_impl(
    input [3:0] x,
    input [3:0] y,
    output [7:0] product
);
    assign product = x * y;
endmodule