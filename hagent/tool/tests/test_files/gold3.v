// Gold comparator module
module comparator(
    input [7:0] a,
    input [7:0] b,
    output greater,
    output equal,
    output less
);
    assign greater = (a > b);
    assign equal = (a == b);
    assign less = (a < b);
endmodule