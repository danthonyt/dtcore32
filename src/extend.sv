import riscv_pkg::*;
module extend (
  // --------------------
  // Instruction input
  // --------------------
  input  logic [31:0] id_q_insn    ,
  // --------------------
  // Control: immediate type
  // --------------------
  input  logic [ 2:0] id_imm_ext_op, // width depends on your enum
  // --------------------
  // Output: extended immediate
  // --------------------
  output logic [31:0] id_imm_ext
);
  // extend immediate to 32 bit value depending on instruction type
  always @(*) begin
    case (id_imm_ext_op)
      //I-type ALU
      I_ALU_TYPE   : id_imm_ext = {{20{id_q_insn[31]}}, id_q_insn[31:20]};
      //S-type
      S_TYPE       : id_imm_ext = {{20{id_q_insn[31]}}, id_q_insn[31:25], id_q_insn[11:7]};
      //B-type
      B_TYPE       : id_imm_ext = {{20{id_q_insn[31]}}, id_q_insn[7], id_q_insn[30:25], id_q_insn[11:8], 1'b0};
      //J-type
      J_TYPE       : id_imm_ext = {{12{id_q_insn[31]}}, id_q_insn[19:12], id_q_insn[20], id_q_insn[30:21], 1'b0};
      //I-type Shift
      I_SHIFT_TYPE : id_imm_ext = {27'd0, id_q_insn[24:20]};
      //U-type lui
      U_TYPE       : id_imm_ext = {id_q_insn[31:12], 12'd0};
      // immediate type CSR instruction
      CSR_TYPE     : id_imm_ext = {27'd0, id_q_insn[19:15]};
      default      : id_imm_ext = 0;
    endcase
  end
endmodule