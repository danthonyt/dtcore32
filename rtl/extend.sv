//===========================================================
// Project    : RISC-V CPU
// File       : extend.sv
// Module     : extend
// Description: Immediate extension unit. Extracts and sign- or 
//              zero-extends immediate values from the instruction 
//              based on the `imm_ext_op_i` type.
//
// Inputs:
//   insn_i        - 32-bit instruction input
//   imm_ext_op_i  - Immediate extension operation type (from enum `imm_ext_op_t`)
//
// Outputs:
//   imm_ext_o     - 32-bit extended immediate value
//
// Notes:
//   - Supports all RISC-V immediate types (I-type, S-type, B-type, U-type, J-type).
//   - Works combinationally; no internal state.
//   - Designed to interface with the ALU input multiplexer in the CPU pipeline.
//
// Author     : David Torres
// Date       : 2025-09-16
//===========================================================

module extend
  import params_pkg::*;
  (
    input logic [31:0] insn_i,
    input imm_ext_op_t imm_ext_op_i,
    output logic [31:0] imm_ext_o
);

  logic [31:0] imm_ext;
  // extend immediate to 32 bit value depending on instruction type
  always_comb begin
    case (imm_ext_op_i)
      //I-type ALU
      I_ALU_TYPE: imm_ext = {{20{insn_i[31]}}, insn_i[31:20]};
      //S-type
      S_TYPE: imm_ext = {{20{insn_i[31]}}, insn_i[31:25], insn_i[11:7]};
      //B-type
      B_TYPE: imm_ext = {{20{insn_i[31]}}, insn_i[7], insn_i[30:25], insn_i[11:8], 1'b0};
      //J-type
      J_TYPE: imm_ext = {{12{insn_i[31]}}, insn_i[19:12], insn_i[20], insn_i[30:21], 1'b0};
      //I-type Shift
      I_SHIFT_TYPE: imm_ext = {27'd0, insn_i[24:20]};
      //U-type lui
      U_TYPE: imm_ext = {insn_i[31:12], 12'd0};
      // immediate type CSR instruction
      CSR_TYPE: imm_ext = {27'd0, insn_i[19:15]};
      default:imm_ext = 0;
    endcase
  end
  assign imm_ext_o = imm_ext;
endmodule
