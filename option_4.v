module and_gate_behavioral(output reg Y, input A, input B);
    reg A_intermediate;
    
    // First always block: isolate A (CRITICAL: breaking long combinational path)
    always @(A) begin
        A_intermediate = A;
    end

    // Second always block: compute the final Y using the intermediate signal and B
    always @(A_intermediate or B) begin
        Y = A_intermediate & B;
    end
endmodule
