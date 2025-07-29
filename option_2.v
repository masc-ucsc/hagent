module and_gate_behavioral(output reg Y, input A, input B);
    // Intermediate signal preserves the word‐instantiation; splitting the logic
    reg intermed;

    // CRITICAL: compute the AND of A and B
    always @(A or B) begin
        intermed = A & B;
    end

    // Use a separate always block to drive Y; functionally equivalent to the original
    always @(A or B) begin
        Y = intermed;
    end
endmodule
