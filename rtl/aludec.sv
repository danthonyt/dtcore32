
module aludec (
    input logic [1:0] alu_op_i,
    input logic rtype_alt_i,
    input logic itype_alt_i,
    input logic [2:0] funct3_i,
    output logic [3:0] alu_control_o
);
  import params_pkg::*;
  logic [3:0] alu_control;
  always_comb begin
    alu_control = 0;
    case (alu_op_i)
      //I-type Load, S-type, U-type
      ALU_OP_ILOAD_S_U_TYPE:
      alu_control = ADD_ALU_CONTROL;  //add- lw,sw,lb,lh,lbu,lhu,sb,sh,auipc,lui
      //B-type
      ALU_OP_B_TYPE:
      case (funct3_i)
        FUNCT3_BEQ: alu_control = SUB_ALU_CONTROL;  //sub - beq
        FUNCT3_BNE: alu_control = BNE_ALU_CONTROL;  //sub - bne
        FUNCT3_BLT: alu_control = LT_ALU_CONTROL;  //blt
        FUNCT3_BGE: alu_control = GE_ALU_CONTROL;  //bge
        FUNCT3_BLTU: alu_control = LTU_ALU_CONTROL;  //bltu
        FUNCT3_BGEU: alu_control = GEU_ALU_CONTROL;  //bgeu
        default: ;
      endcase
      //R-type, I-type ALU,I-type logical shift
      ALU_OP_IALU_ISHIFT_R_TYPE: begin
        case (funct3_i)
          FUNCT3_ADD:
          alu_control = (rtype_alt_i) ? SUB_ALU_CONTROL  /*sub*/ : ADD_ALU_CONTROL  /*add*/;
          FUNCT3_SLL: alu_control = L_SHIFT_ALU_CONTROL;  //sll
          FUNCT3_SLT: alu_control = LT_ALU_CONTROL;  //slt
          FUNCT3_SLTU_SLTIU: alu_control = LTU_ALU_CONTROL;  //sltu, sltiu
          FUNCT3_XOR: alu_control = XOR_ALU_CONTROL;  //xor
          FUNCT3_SRA:
          alu_control = (rtype_alt_i || itype_alt_i) ? R_SHIFT_A_ALU_CONTROL /*sra*/ : R_SHIFT_L_ALU_CONTROL /*srl*/;
          FUNCT3_OR: alu_control = OR_ALU_CONTROL;  //or
          FUNCT3_AND: alu_control = AND_ALU_CONTROL;  //and
          default: ;
        endcase
      end
      default: ;
    endcase
  end
assign alu_control_o = alu_control;
endmodule
