module and_gate_behavioral(output reg Y, input A, input B);
    reg intermediate;

    // First stage: compute the AND – CRITICAL part split for improved timing.
    always @(A or B) begin
        intermediate = A & B;
    end

    // Second stage: drive output using the intermediate result.
    always @(intermediate) begin
        Y = intermediate;
    end
endmodule
