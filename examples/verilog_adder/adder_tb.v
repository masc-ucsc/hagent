`timescale 1ns/1ps

module adder_tb;
    // Testbench signals
    reg [3:0] a, b;
    reg cin;
    wire [3:0] sum;
    wire cout;
    
    // Instantiate the adder
    adder dut (
        .a(a),
        .b(b),
        .cin(cin),
        .sum(sum),
        .cout(cout)
    );
    
    // Test stimulus
    initial begin
        $display("Starting 4-bit Adder Testbench");
        $display("a\tb\tcin\tsum\tcout\tExpected");
        $display("----------------------------------------");
        
        // Test case 1: 5 + 3 = 8
        a = 4'b0101; b = 4'b0011; cin = 1'b0;
        #10;
        $display("%b\t%b\t%b\t%b\t%b\t5+3=8", a, b, cin, sum, cout);
        
        // Test case 2: 7 + 8 = 15 (with carry)
        a = 4'b0111; b = 4'b1000; cin = 1'b0;
        #10;
        $display("%b\t%b\t%b\t%b\t%b\t7+8=15", a, b, cin, sum, cout);
        
        // Test case 3: 15 + 1 = 16 (overflow)
        a = 4'b1111; b = 4'b0001; cin = 1'b0;
        #10;
        $display("%b\t%b\t%b\t%b\t%b\t15+1=16", a, b, cin, sum, cout);
        
        // Test case 4: With carry input
        a = 4'b0000; b = 4'b0000; cin = 1'b1;
        #10;
        $display("%b\t%b\t%b\t%b\t%b\t0+0+1=1", a, b, cin, sum, cout);
        
        // Test case 5: 10 + 6 = 16
        a = 4'b1010; b = 4'b0110; cin = 1'b0;
        #10;
        $display("%b\t%b\t%b\t%b\t%b\t10+6=16", a, b, cin, sum, cout);
        
        $display("----------------------------------------");
        $display("Testbench completed successfully");
        $finish;
    end
    
    // Optional: Monitor signals
    initial begin
        $monitor("Time=%0t a=%b b=%b cin=%b sum=%b cout=%b", 
                 $time, a, b, cin, sum, cout);
    end
    
endmodule
