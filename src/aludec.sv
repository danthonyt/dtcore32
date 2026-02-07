import riscv_pkg::*;
module aludec (
  // Clock & Reset (optional if purely combinational)
  input  logic        clk_i,    // can be ignored if fully combinational
  input  logic        rst_i,    // can be ignored if fully combinational

  // Instruction / opcode inputs
  input  logic [2:0]  id_funct3,      // funct3 from instruction
  input  logic        id_rtype_alt,   // alternative funct7 for R-type
  input  logic        id_itype_alt,   // alternative funct7 for I-type shifts
  input  logic [ALU_OP_T_WIDTH-1:0]  alu_op,         // ALU op type (from control unit)

  // ALU control output
  output logic [ALU_CTRL_T_WIDTH-1:0]  alu_control     // determined ALU operation
);

  always @(*) begin
    alu_control = ADD_ALU_CONTROL;
    case (alu_op)
      //I-type Load, S-type, U-type
      ALU_OP_ILOAD_S_U_TYPE :
        alu_control = ADD_ALU_CONTROL;  //add- lw,sw,lb,lh,lbu,lhu,sb,sh,auipc,lui
      //B-type
      ALU_OP_B_TYPE :
        case (id_funct3)
          FUNCT3_BEQ  : alu_control = SUB_ALU_CONTROL;  //sub - beq
          FUNCT3_BNE  : alu_control = NE_ALU_CONTROL;  //sub - bne
          FUNCT3_BLT  : alu_control = LT_ALU_CONTROL;  //blt
          FUNCT3_BGE  : alu_control = GE_ALU_CONTROL;  //bge
          FUNCT3_BLTU : alu_control = LTU_ALU_CONTROL;  //bltu
          FUNCT3_BGEU : alu_control = GEU_ALU_CONTROL;  //bgeu
          default     : ;
        endcase
      //R-type, I-type ALU,I-type 1al shift
      ALU_OP_IALU_ISHIFT_R_TYPE : begin
        case (id_funct3)
          FUNCT3_ADD :
            alu_control = (id_rtype_alt) ? SUB_ALU_CONTROL  /*sub*/ : ADD_ALU_CONTROL  /*add*/;
          FUNCT3_SLL        : alu_control = L_SHIFT_ALU_CONTROL;  //sll
          FUNCT3_SLT        : alu_control = LT_ALU_CONTROL;  //slt
          FUNCT3_SLTU_SLTIU : alu_control = LTU_ALU_CONTROL;  //sltu, sltiu
          FUNCT3_XOR        : alu_control = XOR_ALU_CONTROL;  //xor
          FUNCT3_SRA        :
            alu_control = (id_rtype_alt || id_itype_alt) ? R_SHIFT_A_ALU_CONTROL /*sra*/ : R_SHIFT_L_ALU_CONTROL /*srl*/;
          FUNCT3_OR  : alu_control = OR_ALU_CONTROL;  //or
          FUNCT3_AND : alu_control = AND_ALU_CONTROL;  //and
          default    : ;
        endcase
      end
      default : ;
    endcase
  end

endmodule
