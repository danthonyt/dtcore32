`include "macros.svh"
module dtcore32_controller(
    input logic clk_i,rst_i,
    input logic [6:0]  op_i,
    input logic [2:0]  funct3_i,
    input logic funct7b5_i,
    output logic [1:0]  ID_result_src_o,
    output logic [1:0]  ID_alu_a_src_o,
    output logic [1:0]  ID_mem_wr_size_o,
    output logic [3:0]  ID_alu_control_o,
    output logic [2:0]  ID_imm_src_o,
    output logic [2:0] ID_load_size_o,
    output logic ID_alu_b_src_o,
    output logic ID_reg_wr_o,
    output logic ID_jump_o,
    output logic ID_branch_o,
    output logic ID_pc_target_alu_src_o,
    output logic ID_is_nop_o,
    output logic ID_exception_o
  );

  // ===========================================================================
  // 			          Parameters, Registers, and Wires
  // ===========================================================================
  logic ID_is_nop;
  logic ID_exception;
  logic opcode_exception;
  logic ID_alu_op_exception;
  logic [1:0] ID_alu_op;
  logic ID_r_type_sub;
  logic ID_i_type_sub;
  logic [1:0]  ID_result_src;
  logic [1:0]  ID_alu_a_src;
  logic [1:0]  ID_mem_wr_size;
  logic [3:0]  ID_alu_control;
  logic [2:0]  ID_imm_src;
  logic [2:0] ID_load_size;
  logic ID_alu_b_src;
  logic ID_reg_wr;
  logic ID_jump;
  logic ID_branch;
  logic ID_pc_target_alu_src;

  // ===========================================================================
  // 			          Implementation
  // ===========================================================================


  assign ID_r_type_sub = op_i[5] & funct7b5_i;
  assign ID_i_type_sub = ~op_i[5] & funct7b5_i;
  
  

  // exception handling
  always_ff @(posedge clk_i)
  begin
    if (rst_i)
      ID_exception <=0;
    else
      ID_exception <= opcode_exception | ID_alu_op_exception;
  end
  always_comb
  begin
    ID_is_nop = 0;
    opcode_exception = 0;
    case (op_i)
      `OPCODE_LOAD:
      begin
        ID_reg_wr = `REGFILE_WRITE_ENABLE;
        ID_imm_src = `ID_I_ALU_TYPE_IMM_SRC;
        ID_alu_a_src = `ALU_A_SRC_SELECT_REG_DATA;
        ID_alu_b_src = `ALU_B_SRC_SELECT_IMM;
        ID_mem_wr_size = `MEM_NO_DMEM_WR;
        ID_result_src = `RESULT_SRC_SELECT_DMEM_RD_DATA;
        ID_branch = `IS_NOT_BRANCH_INSTR;
        ID_alu_op = `ALU_OP_ILOAD_S_U_TYPE;
        ID_jump = `IS_NOT_JUMP_INSTR;
        ID_pc_target_alu_src = `PC_TARGET_ALU_SRC_SELECT_PC;
        case(funct3_i)
          `FUNCT3_LB:
            ID_load_size = `DMEM_LOAD_SIZE_BYTE;
          `FUNCT3_LH:
            ID_load_size = `DMEM_LOAD_SIZE_HALF;
          `FUNCT3_LW:
            ID_load_size = `DMEM_LOAD_SIZE_WORD;
          `FUNCT3_LBU:
            ID_load_size = `DMEM_LOAD_SIZE_BYTEU;
          `FUNCT3_LHU:
            ID_load_size = `DMEM_LOAD_SIZE_HALFU;
          default:
          begin
            ID_load_size = `DMEM_LOAD_SIZE_NO_LOAD;
            opcode_exception = 1;
          end
        endcase
      end


      // FENCE, ECALL, EBREAK are all NOPs
      `OPCODE_FENCE, `OPCODE_SYSTEM:
      begin
        ID_reg_wr = `REGFILE_WRITE_ENABLE;
        ID_alu_a_src = `ALU_A_SRC_SELECT_REG_DATA;
        ID_alu_b_src = `ALU_B_SRC_SELECT_IMM;
        ID_mem_wr_size = `MEM_NO_DMEM_WR;
        ID_result_src = `RESULT_SRC_SELECT_ALU_RESULT;
        ID_branch = `IS_NOT_BRANCH_INSTR;
        ID_alu_op = `ALU_OP_IALU_ISHIFT_R_TYPE;
        ID_jump = `IS_NOT_JUMP_INSTR;
        ID_load_size = `DMEM_LOAD_SIZE_NO_LOAD;
        ID_pc_target_alu_src = `PC_TARGET_ALU_SRC_SELECT_PC;
        ID_imm_src = `ID_I_ALU_TYPE_IMM_SRC;
        ID_is_nop = 1; //addi x0,x0,0
      end


      `OPCODE_STORE:
      begin
        ID_reg_wr = `REGFILE_WRITE_DISABLE;
        ID_imm_src = `ID_S_TYPE_IMM_SRC;
        ID_alu_a_src = `ALU_A_SRC_SELECT_REG_DATA;
        ID_alu_b_src = `ALU_B_SRC_SELECT_IMM;
        ID_load_size = `DMEM_LOAD_SIZE_NO_LOAD;
        ID_result_src = `RESULT_SRC_NO_WRITEBACK;
        ID_branch = `IS_NOT_BRANCH_INSTR;
        ID_alu_op = `ALU_OP_ILOAD_S_U_TYPE;
        ID_jump = `IS_NOT_JUMP_INSTR;
        ID_pc_target_alu_src = `PC_TARGET_ALU_SRC_SELECT_PC;
        case(funct3_i)
          `FUNCT3_SB:
            ID_mem_wr_size = `MEM_BYTE_WR;	//sb
          `FUNCT3_SH:
            ID_mem_wr_size = `MEM_HALF_WR;	//sh
          `FUNCT3_SW:
            ID_mem_wr_size = `MEM_WORD_WR;	//sw
          default:
          begin
            ID_mem_wr_size = `MEM_NO_DMEM_WR;	//unknown instruction
            opcode_exception = 1;
          end
        endcase
      end
      `OPCODE_R_TYPE:
      begin
        ID_reg_wr = `REGFILE_WRITE_ENABLE;
        ID_imm_src = `ID_NO_IMM_SRC;
        ID_alu_a_src = `ALU_A_SRC_SELECT_REG_DATA;
        ID_alu_b_src = `ALU_B_SRC_SELECT_REG_DATA;
        ID_load_size = `DMEM_LOAD_SIZE_NO_LOAD;
        ID_result_src = `RESULT_SRC_SELECT_ALU_RESULT;
        ID_branch = `IS_NOT_BRANCH_INSTR;
        ID_alu_op = `ALU_OP_IALU_ISHIFT_R_TYPE;
        ID_jump = `IS_NOT_JUMP_INSTR;
        ID_pc_target_alu_src = `PC_TARGET_ALU_SRC_SELECT_PC;
        ID_mem_wr_size = `MEM_NO_DMEM_WR;
      end
      `OPCODE_B_TYPE:
      begin
        ID_reg_wr = `REGFILE_WRITE_DISABLE;
        ID_imm_src = `ID_B_TYPE_IMM_SRC;
        ID_alu_a_src = `ALU_A_SRC_SELECT_REG_DATA;
        ID_alu_b_src = `ALU_B_SRC_SELECT_REG_DATA;
        ID_mem_wr_size = `MEM_NO_DMEM_WR;
        ID_result_src = `RESULT_SRC_NO_WRITEBACK;
        ID_branch = `IS_BRANCH_INSTR;
        ID_alu_op = `ALU_OP_B_TYPE;
        ID_jump = `IS_NOT_JUMP_INSTR;
        ID_load_size = `DMEM_LOAD_SIZE_NO_LOAD;
        ID_pc_target_alu_src = `PC_TARGET_ALU_SRC_SELECT_PC;
      end
      //I-type ALU or shift
      `OPCODE_I_TYPE:
      begin
        ID_reg_wr = `REGFILE_WRITE_ENABLE;
        ID_alu_a_src = `ALU_A_SRC_SELECT_REG_DATA;
        ID_alu_b_src = `ALU_B_SRC_SELECT_IMM;
        ID_mem_wr_size = `MEM_NO_DMEM_WR;
        ID_result_src = `RESULT_SRC_SELECT_ALU_RESULT;
        ID_branch = `IS_NOT_BRANCH_INSTR;
        ID_alu_op = `ALU_OP_IALU_ISHIFT_R_TYPE;
        ID_jump = `IS_NOT_JUMP_INSTR;
        ID_load_size = `DMEM_LOAD_SIZE_NO_LOAD;
        ID_pc_target_alu_src = `PC_TARGET_ALU_SRC_SELECT_PC;
        case (funct3_i)
          3'b000,3'b010,3'b011,3'b100,3'b110,3'b111:
            ID_imm_src = `ID_I_ALU_TYPE_IMM_SRC; //I-type ALU
          3'b001,3'b101:
            ID_imm_src = `ID_I_SHIFT_TYPE_IMM_SRC;	//I-type Shift
          default:
          begin
            ID_imm_src = `ID_I_ALU_TYPE_IMM_SRC;	//unknown instruction
            opcode_exception = 1;
          end
        endcase											//I-type shift
      end

      `OPCODE_JAL:
      begin
        ID_reg_wr = `REGFILE_WRITE_ENABLE;
        ID_imm_src = `ID_J_TYPE_IMM_SRC;
        ID_alu_a_src = `ALU_A_SRC_SELECT_REG_DATA;
        ID_alu_b_src = `ALU_B_SRC_SELECT_REG_DATA;
        ID_mem_wr_size = `MEM_NO_DMEM_WR;
        ID_result_src = `RESULT_SRC_SELECT_NEXT_INSTR_ADDR;
        ID_branch = `IS_NOT_BRANCH_INSTR;
        ID_alu_op = `ALU_OP_ILOAD_S_U_TYPE; // TODO
        ID_jump = `IS_JUMP_INSTR;
        ID_load_size = `DMEM_LOAD_SIZE_NO_LOAD;
        ID_pc_target_alu_src = `PC_TARGET_ALU_SRC_SELECT_PC;
      end

      `OPCODE_U_TYPE_LUI:
      begin
        ID_reg_wr = `REGFILE_WRITE_ENABLE;
        ID_imm_src = `ID_U_TYPE_IMM_SRC;
        ID_alu_a_src = `ALU_A_SRC_SELECT_ZERO;
        ID_alu_b_src = `ALU_B_SRC_SELECT_IMM;
        ID_mem_wr_size = `MEM_NO_DMEM_WR;
        ID_result_src = `RESULT_SRC_SELECT_ALU_RESULT;
        ID_branch = `IS_NOT_BRANCH_INSTR;
        ID_alu_op = `ALU_OP_ILOAD_S_U_TYPE;
        ID_jump = `IS_NOT_JUMP_INSTR;
        ID_load_size = `DMEM_LOAD_SIZE_NO_LOAD;
        ID_pc_target_alu_src = `PC_TARGET_ALU_SRC_SELECT_PC;
      end
      `OPCODE_U_TYPE_AUIPC:
      begin
        ID_reg_wr = `REGFILE_WRITE_ENABLE;
        ID_imm_src = `ID_U_TYPE_IMM_SRC;
        ID_alu_a_src = `ALU_A_SRC_SELECT_PC;
        ID_alu_b_src = `ALU_B_SRC_SELECT_IMM;
        ID_mem_wr_size = `MEM_NO_DMEM_WR;
        ID_result_src = `RESULT_SRC_SELECT_ALU_RESULT;
        ID_branch = `IS_NOT_BRANCH_INSTR;
        ID_alu_op = `ALU_OP_ILOAD_S_U_TYPE;
        ID_jump = `IS_NOT_JUMP_INSTR;
        ID_load_size = `DMEM_LOAD_SIZE_NO_LOAD;
        ID_pc_target_alu_src = `PC_TARGET_ALU_SRC_SELECT_PC;
      end
      `OPCODE_JALR:
      begin
        ID_reg_wr = `REGFILE_WRITE_ENABLE;
        ID_imm_src = `ID_I_ALU_TYPE_IMM_SRC;
        ID_alu_a_src = `ALU_A_SRC_SELECT_REG_DATA;
        ID_alu_b_src = `ALU_B_SRC_SELECT_IMM;
        ID_mem_wr_size = `MEM_NO_DMEM_WR;
        ID_result_src = `RESULT_SRC_SELECT_NEXT_INSTR_ADDR;
        ID_branch = `IS_NOT_BRANCH_INSTR;
        ID_alu_op = `ALU_OP_ILOAD_S_U_TYPE;
        ID_jump = `IS_JUMP_INSTR;
        ID_load_size = `DMEM_LOAD_SIZE_NO_LOAD;
        ID_pc_target_alu_src = `PC_TARGET_ALU_SRC_SELECT_REG_DATA;
      end
      default:
      begin
        ID_reg_wr = `REGFILE_WRITE_ENABLE;
        ID_alu_a_src = `ALU_A_SRC_SELECT_REG_DATA;
        ID_alu_b_src = `ALU_B_SRC_SELECT_IMM;
        ID_mem_wr_size = `MEM_NO_DMEM_WR;
        ID_result_src = `RESULT_SRC_SELECT_ALU_RESULT;
        ID_branch = `IS_NOT_BRANCH_INSTR;
        ID_alu_op = `ALU_OP_IALU_ISHIFT_R_TYPE;
        ID_jump = `IS_NOT_JUMP_INSTR;
        ID_load_size = `DMEM_LOAD_SIZE_NO_LOAD;
        ID_pc_target_alu_src = `PC_TARGET_ALU_SRC_SELECT_PC;	//unknown instruction default to i type
        ID_imm_src = `ID_I_ALU_TYPE_IMM_SRC; //I-type ALU
        opcode_exception = 1;
      end

    endcase

  end

  always_comb
  begin
    ID_alu_op_exception = 0;
    case (ID_alu_op)
      //I-type Load, S-type, U-type
      `ALU_OP_ILOAD_S_U_TYPE:
        ID_alu_control = `EX_ADD_ALU_CONTROL; //add- lw,sw,lb,lh,lbu,lhu,sb,sh,auipc,lui
      //B-type
      `ALU_OP_B_TYPE:
      case (funct3_i)
        `FUNCT3_BEQ:
          ID_alu_control = `EX_SUB_ALU_CONTROL; //sub - beq
        `FUNCT3_BNE:
          ID_alu_control = `EX_BNE_ALU_CONTROL; //sub - bne
        `FUNCT3_BLT:
          ID_alu_control = `EX_LT_ALU_CONTROL; //blt
        `FUNCT3_BGE:
          ID_alu_control = `EX_GE_ALU_CONTROL; //bge
        `FUNCT3_BLTU:
          ID_alu_control = `EX_LTU_ALU_CONTROL; //bltu
        `FUNCT3_BGEU:
          ID_alu_control = `EX_GEU_ALU_CONTROL; //bgeu

        default:
        begin
          ID_alu_control = 0; //unknown
          ID_alu_op_exception = 1;
        end

      endcase
      //R-type, I-type ALU,I-type logical shift
      `ALU_OP_IALU_ISHIFT_R_TYPE:
      case (funct3_i)
        `FUNCT3_ADD_SUB:
          ID_alu_control = (ID_r_type_sub) ? `EX_SUB_ALU_CONTROL /*sub*/ : `EX_ADD_ALU_CONTROL /*add*/;
        `FUNCT3_SLL:
          ID_alu_control = `EX_L_SHIFT_ALU_CONTROL; //sll
        `FUNCT3_SLT:
          ID_alu_control = `EX_LT_ALU_CONTROL; //slt
        `FUNCT3_SLTU:
          ID_alu_control = `EX_LTU_ALU_CONTROL; //sltu
        `FUNCT3_XOR:
          ID_alu_control = `EX_XOR_ALU_CONTROL; //xor
        `FUNCT3_SRA_SRL:
          ID_alu_control = (ID_r_type_sub || ID_i_type_sub) ? `EX_R_SHIFT_A_ALU_CONTROL /*sra*/ : `EX_R_SHIFT_L_ALU_CONTROL /*srl*/;
        `FUNCT3_OR:
          ID_alu_control = `EX_OR_ALU_CONTROL; //or
        `FUNCT3_AND:
          ID_alu_control = `EX_AND_ALU_CONTROL; //and
        default:
        begin
          ID_alu_control = 0; //unknown
          ID_alu_op_exception = 1;
        end
      endcase
      default:
      begin
        ID_alu_control = 0; //unknown
        ID_alu_op_exception = 1;
      end
    endcase
  end
  // outputs
  assign ID_exception_o = ID_exception;
  assign ID_is_nop_o = ID_is_nop;
  assign ID_alu_control_o = ID_is_nop ? 0 : ID_alu_control;
  assign ID_result_src_o = ID_result_src;
  assign ID_alu_a_src_o = ID_alu_a_src;
  assign ID_mem_wr_size_o = ID_mem_wr_size;
  assign ID_imm_src_o = ID_imm_src;
  assign ID_load_size_o = ID_load_size;
  assign ID_alu_b_src_o = ID_alu_b_src;
  assign ID_reg_wr_o = ID_reg_wr;
  assign ID_jump_o = ID_jump;
  assign ID_branch_o = ID_branch;
  assign ID_pc_target_alu_src_o = ID_pc_target_alu_src;

endmodule



