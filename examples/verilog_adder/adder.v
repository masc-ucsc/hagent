// 4-bit Ripple Carry Adder
module adder(
    input [3:0] a,      // First 4-bit input
    input [3:0] b,      // Second 4-bit input
    input cin,          // Carry input
    output [3:0] sum,   // 4-bit sum output
    output cout         // Carry output
);

    // Internal carry signals
    wire c1, c2, c3;
    
    // Full adder instances
    full_adder fa0 (.a(a[0]), .b(b[0]), .cin(cin),  .sum(sum[0]), .cout(c1));
    full_adder fa1 (.a(a[1]), .b(b[1]), .cin(c1),   .sum(sum[1]), .cout(c2));
    full_adder fa2 (.a(a[2]), .b(b[2]), .cin(c2),   .sum(sum[2]), .cout(c3));
    full_adder fa3 (.a(a[3]), .b(b[3]), .cin(c3),   .sum(sum[3]), .cout(cout));

endmodule

// Full Adder Module
module full_adder(
    input a,
    input b,
    input cin,
    output sum,
    output cout
);
    
    assign sum = a ^ b ^ cin;
    assign cout = (a & b) | (cin & (a ^ b));
    
endmodule
