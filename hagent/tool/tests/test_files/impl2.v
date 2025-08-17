// Implementation file 2 with comparator
module cmp_impl(
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