module and_gate_behavioral(output reg Y, input A, input B);
    reg intermediate;
    
    // First always block computes the critical combinational operation.
    always @(*) begin
        intermediate = A & B;
    end

    // Second always block transfers the intermediate result to the output.
    always @(*) begin
        Y = intermediate;
    end
endmodule
