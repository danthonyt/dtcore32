import riscv_pkg::*;
module extend (
  // --------------------
  // Instruction input
  // --------------------
  input  logic [31:0] insn    ,
  // --------------------
  // Control: immediate type
  // --------------------
  input  logic [ IMM_EXT_OP_T_WIDTH-1:0] op, // width depends on your enum
  // --------------------
  // Output: extended immediate
  // --------------------
  output logic [31:0] imm_ext
);
  // extend immediate to 32 bit value depending on instruction type
  always_comb begin
    case (op)
      //I-type ALU
      I_ALU_TYPE   : imm_ext = {{20{insn[31]}}, insn[31:20]};
      //S-type
      S_TYPE       : imm_ext = {{20{insn[31]}}, insn[31:25], insn[11:7]};
      //B-type
      B_TYPE       : imm_ext = {{20{insn[31]}}, insn[7], insn[30:25], insn[11:8], 1'b0};
      //J-type
      J_TYPE       : imm_ext = {{12{insn[31]}}, insn[19:12], insn[20], insn[30:21], 1'b0};
      //I-type Shift
      I_SHIFT_TYPE : imm_ext = {27'd0, insn[24:20]};
      //U-type lui
      U_TYPE       : imm_ext = {insn[31:12], 12'd0};
      // immediate type CSR instruction
      CSR_TYPE     : imm_ext = {27'd0, insn[19:15]};
      default      : imm_ext = 0;
    endcase
  end
endmodule