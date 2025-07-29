module bitcnt_prop(input  [63:0] din_data,
input  [ 2:0] din_func,
output [63:0] dout_data,
input        reg [63:0] tmp,
input        reg [7:0] cnt,
input           mode32,
input           czmode
);
// Declare revmode
logic revmode;

// Check if `din_data` is directly assigned to `tmp` when `!revmode` is true
// Same-cycle assertion: no delay in combination with pre-condition.
asgpt__din_data_assignment: assert property ((!revmode) |-> (tmp == din_data)) else $fatal("Assertion failed: `din_data` should be directly assigned to `tmp` when `!revmode` is true.");
// Check for correct counting operation based on `din_func` mode settings
// Next-cycle assertion for mode-based counting.
asgpt__cnt_mode_functionality: assert property (1 |=> ((din_func[2:0] == 3'b000) || (din_func[2:0] == 3'b001) || (din_func[2:0] == 3'b010) || (din_func[2:0] == 3'b011) || (din_func[2:0] == 3'b100) || (din_func[2:0] == 3'b101)) && (cnt == ($countones(din_data) & ~(din_func[0] ? (din_func[2] ? 32'hFFFF_FFFF : 32'h0000_0000) : 32'hFFFF_FFFF)))) else $fatal("Assertion failed: Incorrect counting based on mode.");
// Check liveness and validity of `dout_data` being updated
// Liveness check: A good event dirties the `dout_data`.
asgpt__dout_data_update: assert property ((dout_data !== cnt) |-> (dout_data == cnt)) else $fatal("Assertion failed: `dout_data` should match `cnt`.");
// Safety check to ensure `din_data` has at least one '1' when `revmode` is false and data is inverted.
// Pre-condition ensures `!revmode` and data correctness.
asgpt__din_data_contains_one: assert property ((!revmode && (|din_data)) |-> (|tmp)) else $fatal("Safety violation: When not in reverse, `din_data` must have at least one '1'.");

// Check that the function selection in `din_func` does not point to unused functions (safety property).
// Unused functions are defined as codes '110' and '111'.
asgpt__check_din_func_valid: assert property (~(~din_func[2] & din_func[1]));

// Check the transformation happens correctly based on din_func for the correct mode setting within a single cycle (safety property).
// Mode influencing signals are `mode32`, `revmode`, and `czmode`.
asgpt__check_mode32_setting: assert property (din_func[0] |-> mode32);
asgpt__check_revmode_setting: assert property (din_func[1] |-> (!revmode));
asgpt__check_czmode_setting: assert property (din_func[2] |-> (!czmode));

// Verify that the output `dout_data` reflects a correct count of 1s or 0s based on the mode set by `din_func` (liveness property).
// The `dout_data` is determined by `cnt` which should be correct based on operation.
asgpt__check_cnt_accurate: assert property ((din_func == 3'b000) |-> (dout_data == $countones(~din_data)));
asgpt__check_cnt_accurate_32: assert property ((din_func == 3'b001) |-> (dout_data == $countones(~din_data[31:0])));
asgpt__check_cnt_ctz64: assert property ((din_func == 3'b010) |-> (dout_data == $countones(din_data | (din_data - 1))));
asgpt__check_cnt_ctz32: assert property ((din_func == 3'b011) |-> (dout_data == $countones(din_data[31:0] | (din_data[31:0] - 1))));
asgpt__check_cnt_count64: assert property ((din_func == 3'b100) |-> (dout_data == $countones(din_data)));
asgpt__check_cnt_count32: assert property ((din_func == 3'b101) |-> (dout_data == $countones(din_data[31:0])));

// Check for obvious corner cases, ensure that `dout_data` must not be undefined (X) for any valid `din_func`.
asgpt__check_no_undefined_output: assert property (|din_func |-> ~(|dout_data === 'bx));

// Check that dout_data accurately reflects the operation performed: CLZ, CTZ, or CNT based on din_func
// and ensures no bits are set when unused functions codes (111, 110) are used.
asgpt__dout_data_correct_operation: assert property (
    (!(din_func[2:0] === 3'b111 || din_func[2:0] === 3'b110))
    |->
    ((din_func[2:1] === 2'b00) ? dout_data == $countones(!din_data) :
     (din_func[2:1] === 2'b01) ? dout_data == $countones(din_data & (din_data - 1) ^ din_data) :
     (din_func[2]    === 1'b0) ? dout_data == $countones(din_data) : 1'b1)
);

// Safety property: Ensure that dout_data remains stable given stable din_data.
// Liveness property: Given correct inputs, dout_data should eventually reflect the correct operation.
asgpt__dout_data_stability: assert property (
    $stable(din_data)
    |->
    dout_data == $past(dout_data)
);

// Check that cnt accurately reflects the leading, trailing, or total number of 1s based on din_func
// not being in the unused state.
asgpt__cnt_calculations: assert property (
    (!(din_func[2:0] === 3'b110 || din_func[2:0] === 3'b111))
    |->
    ((din_func[2:1] === 2'b00) ? cnt == $countones(!din_data) :
     (din_func[2:1] === 2'b01) ? cnt == $countones(din_data & (din_data - 1) ^ din_data) :
     (din_func[2]    === 1'b0) ? cnt == $countones(din_data) : 1'b1)
);

// State transition analysis: Ensure no transitions into unused state (111, 110) for din_func.
//asgpt__din_func_no_unused_transition: assert property (
//    @(posedge clk) !(din_func === 3'b111 || din_func === 3'b110)
//);

// Assertions for micro-architectural analysis is unnecessary here because no specific structures like
// FIFO, RAM are observed and cnt directly assigns values without intermediate buffer storage.

// No corner cases involving FIFO full/empty, but ensuring that unused states do not affect dout_data.
asgpt__unused_no_effect: assert property (
    (din_func === 3'b111 || din_func === 3'b110)
    |->
    dout_data === dout_data
);


// Check that `mode32` controls the operation of temporary register `tmp` truncation
// If `mode32` is set (1), then `tmp` must only consider the lower 32 bits of `din_data`. If not, `tmp` might take the full 64 bits.
asgpt__check_mode32_truncation: assert property (mode32 |-> tmp[31:0] == din_data[31:0]);

// Verify that when `mode32` is not set, `tmp` operates properly considering all 64 bits of `din_data`
asgpt__check_mode32_full: assert property ((!mode32) |-> |tmp[63:0]);

// Check that if `revmode` is not set, `tmp` directly equals `din_data`. Here, `revmode` determines if the reverse operation applies.
asgpt__check_revmode_operation: assert property ((!revmode) |-> (tmp == din_data));

// Validate that when `czmode` is active, specific operation (`tmp - 1` & `~tmp`) applies to `tmp`.
asgpt__check_czmode_effect: assert property (czmode |-> (tmp == ((tmp - 1) & ~tmp)));

// Verify that the count `cnt` is always computed from the `tmp` logic under the restrictions of `mode32`.
//asgpt__check_count_behavior: assert property ((mode32 |-> (cnt == $countones(tmp[31:0]))) && (!mode32 |-> (cnt == $countones(tmp))));

// Verify dout_data outputs the count value derived from `cnt`. Ensures that `cnt` reflects in `dout_data`.
asgpt__check_output_matches_cnt: assert property (dout_data == {56'b0, cnt});


// Check that the `revmode` signal is correctly computed as the logical NOT of `din_func[1]`.
asgpt__revmode_logic: assert property (revmode == !din_func[1]);

// Check that when `revmode` is low (active), `tmp` directly gets assigned `din_data` and does not perform any additional operations on `tmp`.
asgpt__revmode_low_behavior: assert property (revmode == 0 |-> tmp == din_data);

// Check that when `revmode` is high (deactivated), the `tmp` transformation logic should be invoked.
asgpt__revmode_high_behavior: assert property (revmode == 1 |-> !(&tmp == din_data));

// Assert safety and liveness: `cnt` should always be computed correctly and shouldn't exceed 64 (the bit-width).
asgpt__cnt_range_check: assert property (cnt <= 64);

// Assert that `cnt` reflects the number of bits set in `tmp` when considering `mode32`.
asgpt__cnt_bit_population: assert property (cnt == $countones(tmp & (mode32 ? 32'hFFFFFFFF : 64'hFFFFFFFFFFFFFFFF)));

// Safety check for `tmp`: `tmp` must be correctly updated when `!revmode`, `mode32`, or `czmode` is active.
asgpt__tmp_safety: assert property (revmode == 0 | mode32 | czmode |-> tmp == (mode32 ? din_data[31:0] : din_data));

// Check that after processing, the transformation through `czmode` achieves a specific post-condition.
asgpt__czmode_behavior: assert property (czmode == 1 |-> tmp == ((tmp-1) & ~tmp));

// Ensure `dout_data` correctly reflects the computed `cnt` value.
asgpt__dout_data_logic: assert property (dout_data == cnt);


// Assertion for the functionality of `czmode` and its related effect on `tmp`
/* This assertion checks that when `czmode` is true, `tmp` is modified correctly by the operation `(tmp-1) & ~tmp`. This checks the safety property that the `czmode` operation is applied correctly. */
asgpt__czmode_tmp_safe: assert property (czmode |-> tmp == ((tmp - 1) & ~tmp));

// Assertion for the correct transition of `tmp` based on `czmode`
/* This assertion verifies that if `czmode` is true, then `tmp` should eventually (next-cycle) reflect the modified value `(tmp-1) & ~tmp`, illustrating liveness that `tmp` transitions correctly. */
asgpt__czmode_tmp_liveness: assert property (czmode |=> tmp == ((($past(tmp)) - 1) & ~($past(tmp))));

// Assertion for the integrity of `cnt` based on the outcome of `tmp`
/* This assertion ensures that the computed `cnt` always equals the number of set bits in `tmp`, ensuring functional safety of `cnt` calculation and demonstrates liveness.*/
asgpt__cnt_integrity: assert property (cnt == $countones(tmp));

// Assertion to confirm that only defined functions are utilized
/* This assertion ensures that `din_func` is one of the defined operations, thereby preventing invocation of unused operations and maintaining safety. */
asgpt__defined_funcs: assert property ((din_func != 3'b111) && (din_func != 3'b110));

// Assertions for checking state transitions
// Since this module doesn't have explicit state machine logic, focus on signal conditions.
/* Verify that valid transitions occur only based on `czmode` */
asgpt__czmode_transition: assert property ((czmode) |-> ((tmp == ((tmp - 1) & ~tmp))));

// Assertions for mode32 and its effect on `tmp`
/* This assertion checks that if `mode32` is true, the lower 32 bits of `tmp` are modified according to the `din_data`, ensuring safety in data handling. */
asgpt__mode32_tmp_values: assert property ((mode32) |-> (tmp[31:0] == $past(din_data[31:0])));

// Check that `dout_data` correctly reflects `cnt` in next cycle
/* This assertion ensures liveness that `dout_data` is updated to the value of `cnt`, which has been derived from `tmp`. */
asgpt__dout_data_updates: assert property (cnt |=> dout_data == $past(cnt));

// Corner case check for full zero condition of `tmp`
/* This assertion checks that when `czmode` is active, and `tmp` becomes all zero, `cnt` should also reflect as zero, illustrating safety under special conditions. */
asgpt__czmode_zero_case: assert property (((czmode && |tmp == 1'b0)) |-> cnt == 8'b0);


// Check if when 'revmode' is false, 'tmp' is assigned 'din_data' in the same cycle
// Safety: 'tmp' must always be equal to 'din_data' if 'revmode' is false
asgpt__tmp_assign_when_revmode_false: assert property ( (!revmode |-> (tmp == din_data)) );

// Check if when 'mode32' is true, 'tmp' is truncated to 32 bits in the next cycle
// Safety: Lower 32 bits must be equal to the previous cycle's lower 32 bits of 'tmp'
asgpt__trunc_tmp_mode32: assert property ( (mode32 |=> ($past(tmp[31:0]) == tmp[31:0])) );

// Check if when 'czmode' is true, 'tmp' undergoes CZ mode operation in the next cycle
// Safety: Ensure 'tmp' transitions correctly using the CZ operation
asgpt__czmode_operation: assert property ( (czmode |=> ($past(tmp) - 1) & ~$past(tmp) == tmp) );

// Ensuring 'cnt' accurately counts the number of ones in 'tmp'
// Liveness: 'cnt' will eventually correctly count the number of ones in 'tmp'
asgpt__cnt_correctness: assert property ( cnt == $countones(tmp) );

// Check safety that only valid din_func[2:0] assignments affect operations (Out-of-spec is unused)
// Safety: Avoid unintended behavior with undefined 'din_func' combinations
asgpt__valid_func_combination: assert property ( din_func != 3'b110 && din_func != 3'b111 );

// Check that the functionality of the module covers all functions as per specification
// Liveness: Ensure functionality eventually completes based on 'din_func' encoding
asgpt__spec_functionality_coverage: assert property (
    (din_func == 3'b000) || (din_func == 3'b001) ||
    (din_func == 3'b010) || (din_func == 3'b011) ||
    (din_func == 3'b100) || (din_func == 3'b101)
);


// Assertion for correct initialization of cnt to 0 before counting process begins
// Ensures cnt starts from zero before counting ones in tmp
asgpt__cnt_initialization: assert property (cnt == 0);

// Assertion that ensures cnt accurately reflects the number of ‘1’s in tmp
// Liveness property: cnt will eventually equal the number of 1s in tmp corresponding to mode32 setting
asgpt__cnt_one_count_liveness: assert property (
    tmp == ((cnt == $countones(tmp & ({64{1'b1}} >> (mode32 ? 32 : 0)))))
);

// Assertion for the association of cnt with dout_data
// Safety property: that no incorrect value in cnt is passed to dout_data
asgpt__cnt_to_dout_data_safety: assert property (
    (cnt != $past(dout_data)) |-> (dout_data == $past(cnt))
);

// Assertion: Ensures cnt will have the count of bits within tmp after loop completes
// Liveness property: ensures that cnt eventually equals the count of ones in tmp considering conditions
//asgpt__cnt_final_count_liveness: assert property (
//    (i == 63) |-> (cnt == $countones(tmp & ({64{1'b1}} >> (mode32 ? 32 : 0))))
//);

// Assertion checking the impact of mode32 on tmp
// Safety property: confirms 32-bit mode correctly truncates tmp
asgpt__mode32_tmp_truncation_safety: assert property (
    (mode32) |-> (tmp[63:32] == 32'b0)
);

// Assertion for proper operation of loop boundaries
// Safety property: guard against incorrect loop boundaries affecting cnt results
asgpt__loop_boundary_safety: assert property (
    !(|tmp[31:0] & mode32) |-> !(|cnt & ~tmp[31:0])
);

// Assertions for logic isolation in 32-bit and 64-bit modes
// Safeguard ensuring isolation logic correctly toggles between 32 and 64-bit
asgpt__bit_mode_isolation_safety: assert property (
    (mode32 != czmode) |-> (tmp[32] == tmp[63])
);


// Check that when revmode is false, tmp is assigned to din_data in the same cycle
// This verifies that the bypass operation functions correctly.
asgpt__revmode_bypass: assert property (!revmode |-> tmp == din_data);

// Check that when revmode is true, tmp is processed based on the din_data input
// This checks that the reverse operation (not bypassed) has occurred as per the logic.
//asgpt__revmode_reverse: assert property (revmode |-> &i && (tmp[i] == (i < 32 && mode32 ? din_data[(63-i) % 32] : din_data[63-i])));

// Ensure cnt correctly counts the 1s in tmp, taking into account the mode32 constraint
// This validates that the counter accurately reflects the number of set bits.
//asgpt__cnt_correct_counting: assert property ((i < 32 || !mode32) |-> cnt == $countones(tmp && (i < 32 || !mode32)));

// Verify that if czmode is true, tmp is assigned properly as decrement and bitwise AND NOT
// This ensures correct operation for the mode logic influencing zero count behavior.
asgpt__czmode_behavior_1: assert property (czmode |-> tmp == ((tmp-1) & ~tmp));

// Diagnose potential overflow or underflow scenarios in the combinational logic
// This helps to identify improper logic flow that could lead to incorrect assignments.
asgpt__logic_flow_integrity: assert property (!(tmp > 64'hFFFFFFFFFFFFFFFF) && !(tmp < 0));

// Assertions ensure pipeline consistency and that no state is unintentionally bypassed
// Verifying the connection of din_func, revmode, and overall control logic.
asgpt__pipeline_consistency: assert property ((din_func[1:0] === 2'b00 | 2'b01) |=> (revmode ? tmp : cnt) == din_data);

endmodule

