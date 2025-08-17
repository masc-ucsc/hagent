<p>
The arithmetic logic unit (ALU) is a small piece of hardware which performs 32 and 64-bit subtraction, addition, shifts and comparisons. It always completes its operation in a single cycle and therefore does not contain any state-full elements. Its ready signal is always asserted and it simply passes the transaction ID from its input to its output. Together with the two operands it also receives an operator which tells it which operation to perform.
</p>
<p>
Table 16. alu module IO ports
</p>
| Signal             | IO  | Description                           | connexion   | Type                    |
| ------------------ | --- | ------------------------------------- | ----------- | ----------------------- |
| `clk_i`            | in  | Subsystem Clock                       | SUBSYSTEM   | logic                   |
| `rst_ni`           | in  | Asynchronous reset active low         | SUBSYSTEM   | logic                   |
| `fu_data_i`        | in  | FU data needed to execute instruction | ISSUE_STAGE | fu_data_t               |
| `result_o`         | out | ALU result                            | ISSUE_STAGE | logic[CVA6Cfg.XLEN-1:0] |
| `alu_branch_res_o` | out | ALU branch compare result             | branch_unit | logic                   |