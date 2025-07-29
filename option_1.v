module and_gate_behavioral(output reg Y, input A, input B);
    reg A_pipe;
    
    // CRITICAL: Break the long combinational path by staging A
    always @(*) begin
        A_pipe = A;
    end

    // CRITICAL: Combine staged A with B
    always @(*) begin
        Y = A_pipe & B;
    end
endmodule
