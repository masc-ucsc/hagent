module and_gate_behavioral(output reg Y, input A, input B);
    // First combinational block calculates the intermediate AND result.
    reg intermediate;
    always @(A or B) begin
        intermediate = A & B;  // CRITICAL: original critical path logic partitioned here
    end

    // Second combinational block registers the intermediate to output.
    always @(intermediate) begin
        Y = intermediate;
    end
endmodule
