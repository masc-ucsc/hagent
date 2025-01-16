module full_adder(
    input [0:0] a,
    input [0:0] b,
    input [0:0] cin,
    output [0:0] sum,
    output [0:0] cout
);
    
    assign sum = ((a == 1 && b == 1) || (a == 1 && cin == 1) || (b == 1 && cin == 1));
    assign cout = (a == 1 && b == 0 && cin == 0);
endmodule