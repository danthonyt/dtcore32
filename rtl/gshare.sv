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
//   pc_lsb10_i              - Lower 10 bits of the branch instruction PC
//   branch_taken_i          - Actual branch outcome (taken/not taken)
//   branch_result_valid_i   - High when branch outcome is valid
//   branch_predict_valid_i  - High when prediction can be updated
//
// Outputs:
//   branch_predict_o        - Predicted branch outcome (taken/not taken)
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
    input logic [9:0] pc_lsb10_i,
    input logic branch_taken_i,
    input logic branch_result_valid_i,
    input logic branch_predict_valid_i,
    output logic branch_predict_o
);
  logic [9:0] branch_history;
  logic [1:0] predictor_arr[0:1023];
  logic [9:0] predictor_index;
  int i;
  assign predictor_index = pc_lsb10_i ^ branch_history;
  // make a branch prediction if the instruction is a branch
  assign branch_predict_o = branch_predict_valid_i ? predictor_arr[predictor_index][1] : 0;
  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      branch_history <= '0;
      for (i = 0; i < 1024; i = i + 1) begin
        predictor_arr[i] <= '0;
      end
    end else begin
      // actual branch result is resolved by the pipeline
      if (branch_result_valid_i) begin
        // store the actual branch result if a branch instruction is resolved 
        branch_history <= {branch_history[8:0], branch_taken_i};
        // update 2 bit branch predictor at index
        // saturate at 2'b00 or 2'b11
        // 2'b11 is branch strongly taken and 
        // 2'b00 is branch strongly not taken
        if (branch_taken_i && (predictor_arr[predictor_index] != 2'b11)) begin
          predictor_arr[predictor_index] <= predictor_arr[predictor_index] + 1;
        end else if (!branch_taken_i && (predictor_arr[predictor_index] != 2'b00)) begin
          predictor_arr[predictor_index] <= predictor_arr[predictor_index] - 1;
        end
      end

    end
  end
endmodule
