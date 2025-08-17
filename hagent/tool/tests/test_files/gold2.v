// Gold multiplier module
module multiplier(
    input [3:0] x,
    input [3:0] y,
    output [7:0] product
);
    assign product = x * y;
endmodule