//===========================================================
// Project    : RISC-V CPU / Branch Prediction
// File       : gshare.sv
// Module     : gshare
// Description: Gshare branch predictor. Uses a global branch 
//              history register (GHR) XORed with the lower bits 
//              of the program counter to index a pattern history 
//              table (PHT) and generate branch predictions.
//
// Inputs:
//   clk_i                   - System clock
//   rst_i                   - Synchronous reset
//   pc_lsb6_i              - Lower 6 bits of the branch instruction PC
//   branch_taken_i          - Actual branch outcome (taken/not taken)
//   branch_result_valid_i   - High when branch outcome is valid
//   branch_predict_valid_i  - High when prediction can be updated
//   mem_pht_idx_i           - Index of pht for branch instruction in MEM stage
//
// Outputs:
//   branch_predict_o        - Predicted branch outcome (taken/not taken)
//   if_pht_idx_o       - Index used to predict the branch. passes through the pipeline
//
// Notes:
//   - Implements standard gshare branch prediction algorithm.
//   - Maintains 2-bit saturating counters for prediction.
//   - Updates prediction table on branch resolution when branch_result_valid_i is high.
//   - Prediction can be used by IF stage to reduce pipeline stalls.
//
// Author     : David Torres
// Date       : 2025-09-16
//===========================================================

module gshare (
    input logic clk_i,
    input logic rst_i,
    input logic [5:0] pc_lsb6_i,
    input logic branch_taken_i,
    input logic branch_result_valid_i,
    input logic branch_predict_valid_i,
    input logic [5:0] mem_pht_idx_i,
    output logic branch_predict_o,
    output logic [5:0] if_pht_idx_o
);
  logic [5:0] ght;
  logic [1:0] pht[0:63];
  logic [5:0] pht_idx;
  int i;
  assign pht_idx  = branch_predict_valid_i ? pc_lsb6_i ^ ght : 0;
  // make a branch prediction if the instruction is a branch
  assign branch_predict_o = branch_predict_valid_i ? pht[pht_idx][1] : 0;
  assign if_pht_idx_o = pht_idx;
  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      ght <= '0;
      for (i = 0; i < 64; i = i + 1) begin
        pht[i] <= 2'b01;
      end
    end else begin
      if (branch_result_valid_i) begin
        // store the actual branch result if a branch instruction is resolved 
        ght <= {ght[4:0], branch_taken_i};
        // update 2 bit branch predictor at index
        // saturate at 2'b00 or 2'b11
        // 2'b11 is branch strongly taken and 
        // 2'b00 is branch strongly not taken
        if (branch_taken_i && (pht[mem_pht_idx_i] != 2'b11)) begin
          pht[mem_pht_idx_i] <= pht[mem_pht_idx_i] + 1;
        end else if (!branch_taken_i && (pht[mem_pht_idx_i] != 2'b00)) begin
          pht[mem_pht_idx_i] <= pht[mem_pht_idx_i] - 1;
        end
      end

    end
  end
endmodule
