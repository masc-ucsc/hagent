// Imported packages

module bitcnt_prop(input  [63:0] din_data,
input  [ 2:0] din_func,
output [63:0] dout_data,
input        reg [63:0] tmp,
input        reg [7:0] cnt
);
// Check if `din_data` is directly assigned to `tmp` when `!revmode` is true
// Same-cycle assertion: no delay in combination with pre-condition.
asgpt__din_data_assignment: assert property ((!revmode) |-> (tmp === din_data)) else $fatal("Assertion failed: `din_data` should be directly assigned to `tmp` when `!revmode` is true.");
// Check for correct counting operation based on `din_func` mode settings
// Next-cycle assertion for mode-based counting.
asgpt__cnt_mode_functionality: assert property (1 |=> (din_func[2:0] == 3'b000 | 3'b001 | 3'b010 | 3'b011 | 3'b100 | 3'b101) | -> cnt === ($countones(din_data) & ~(din_func[0] | (din_func[2] ? 32'h0000_0000FFFFFFFF : 32'hFFFF_FFFF)))) else $fatal("Assertion failed: Incorrect counting based on mode.");
// Check liveness and validity of `dout_data` being updated
// Liveness check: A good event dirties the `dout_data`.
asgpt__dout_data_update: assert property ((dout_data !== cnt) |-> (dout_data == cnt)) else $fatal("Assertion failed: `dout_data` should match `cnt`.");
// Safety check to ensure `din_data` has at least one '1' when `revmode` is false and data is inverted.
// Pre-condition ensures `!revmode` and data correctness.
asgpt__din_data_contains_one: assert property ((!revmode & (|din_data)) |-> (|tmp)) else $fatal("Safety violation: When not in reverse, `din_data` must have at least one '1'.");

endmodule
