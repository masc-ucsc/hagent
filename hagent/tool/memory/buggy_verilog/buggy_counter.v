// Buggy Verilog Counter with intentional bugs
module buggy_counter(
    input clk,
    input reset_n,
    output reg [3:0] count,
    output reg overflow
);
    // Bug 1: Missing output type (should be reg overflow)
    
    // Bug 2: Using negedge instead of posedge
    always @(negedge clk) begin
        // Bug 3: Missing reset logic
        
        // Counter logic with overflow bug
        if (count == 4'b1111) begin
            count <= 0;
            overflow = 1;  // Bug 4: Using blocking assignment
        end else begin
            count <= count + 1;
            overflow = 0;  // Bug 4: Using blocking assignment
        end
    end
endmodule 