
import riscv_pkg::*;
module if_id_pipeline (
  input  logic       clk_i,
  input  logic       rst_i,
  input  logic       if_id_flush,
  input  logic       if_id_stall,
  input  logic       imem_rdata_valid,
  input  logic       if_d_valid,
  input  logic [31:0] if_d_pc,
  input  logic [31:0] if_d_pc_plus_4,
  input  logic [31:0] if_d_insn,
`ifdef RISCV_FORMAL
  input  logic       if_d_intr,
  output logic       id_q_intr,
`endif
  output logic       id_q_valid,
  output logic [31:0] id_q_pc,
  output logic [31:0] id_q_pc_plus_4,
  output logic [31:0] id_q_insn
);

//-------------------------------
// IF/ID pipeline
//-------------------------------
  always_ff @(posedge clk_i) begin
    // clear the pipeline on reset, flush,
    // or imem buffer invalid AND the
    // stage is not stalled
    if (rst_i || if_id_flush || (!if_id_stall && !imem_rdata_valid)) begin
      // clear all IF/ID pipeline registers
      id_q_valid     <= 0;
      id_q_pc        <= 0;
      id_q_pc_plus_4 <= 0;
      id_q_insn      <= NOP_INSTRUCTION;
`ifdef RISCV_FORMAL
      id_q_intr <= 0;
`endif
    end else if (!if_id_stall) begin
      // propagate IF stage outputs to ID stage
      id_q_valid     <= if_d_valid;
      id_q_pc        <= if_d_pc;
      id_q_pc_plus_4 <= if_d_pc_plus_4;
      id_q_insn      <= if_d_insn;
`ifdef RISCV_FORMAL
      id_q_intr <= if_d_intr;
`endif
    end
  end

endmodule
