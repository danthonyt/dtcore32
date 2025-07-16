`include "macros.svh"
module dtcore32_decode_unit(
    input logic clk_i,
    input logic rst_i,
    // ID signals
    input logic [31:0] ID_instr_i,
    output logic ID_dmem_read_o,
    output logic [1:0]  ID_result_src_o,
    output logic [1:0]  ID_alu_a_src_o,
    output logic [1:0]  ID_mem_wr_size_o,
    output logic [3:0]  ID_alu_control_o,
    output logic [2:0] ID_load_size_o,
    output logic  ID_alu_b_src_o,
    output logic ID_reg_wr_en_o,
    output logic ID_jump_o,
    output logic ID_branch_o,
    output logic ID_pc_target_alu_src_o,
    output logic ID_exception_o,
    output logic [4:0] ID_src_reg_1_o,
    output logic [4:0] ID_src_reg_2_o,
    output logic [4:0] ID_dest_reg_o,
    output logic [31:0] ID_imm_ext_o,
    output logic ID_is_ecall_o
  );
  // ===========================================================================
  // 			          Parameters, Registers, and Wires
  // ===========================================================================
  
  // immediate extend unit signals
  logic [2:0] ID_imm_src;
  logic [31:0] ID_imm_ext_tmp;

  // opcode decoder signals 
  logic opcode_exception;
  logic [6:0]  op;
  logic [2:0]  funct3;
  logic funct7b5;
  
  // alu operation decoder signals
  logic ID_alu_op_exception;
  logic [1:0] ID_alu_op;
  logic ID_r_type_sub;
  logic ID_i_type_sub;
  logic [3:0]  ID_alu_control;

  logic ID_is_nop;


  // ===========================================================================
  // 			          Implementation
  // ===========================================================================

  assign op = ID_instr_i[6:0];
  assign funct3 = ID_instr_i[14:12];
  assign funct7b5 = ID_instr_i[30];
  assign ID_r_type_sub = op[5] & funct7b5;
  assign ID_i_type_sub = ~op[5] & funct7b5;
  assign ID_alu_control_o = ID_is_nop ? 0 : ID_alu_control;

  assign ID_src_reg_1_o = ID_is_nop ? 0 : ID_instr_i[19:15];
  assign ID_src_reg_2_o = ID_is_nop ? 0 : ID_instr_i[24:20];
  assign ID_dest_reg_o = ID_is_nop ? 0 : ID_instr_i[11:7];
  assign ID_imm_ext_o = ID_is_nop ? 0 : ID_imm_ext_tmp;



  // extend immediate to 32 bit value depending on instruction type
  always_comb
  begin
    case (ID_imm_src)
      //I-type ALU
      3'b000:
        ID_imm_ext_tmp = { {20{ID_instr_i[31]}}, ID_instr_i[31:20] };
      //S-type
      3'b001:
        ID_imm_ext_tmp = { {20{ID_instr_i[31]}}, ID_instr_i[31:25], ID_instr_i[11:7] };
      //B-type
      3'b010:
        ID_imm_ext_tmp = { {20{ID_instr_i[31]}}, ID_instr_i[7], ID_instr_i[30:25], ID_instr_i[11:8], 1'b0};
      //J-type
      3'b011:
        ID_imm_ext_tmp = { {12{ID_instr_i[31]}}, ID_instr_i[19:12], ID_instr_i[20], ID_instr_i[30:21], 1'b0};
      //I-type Shift
      3'b100:
        ID_imm_ext_tmp = { 27'd0, ID_instr_i[24:20]};
      //U-type lui
      3'b101:
        ID_imm_ext_tmp = { ID_instr_i[31:12] , 12'd0 };
      default:
        ID_imm_ext_tmp = 0;
    endcase
  end

  // exception when the instruction is unknown
  always_ff @(posedge clk_i)
  begin
    if (rst_i)
      ID_exception_o <= 0;
    else
      ID_exception_o <= opcode_exception | ID_alu_op_exception;
  end
  always_comb
  begin
    ID_is_nop = 0;
    ID_is_ecall_o = 0;
    opcode_exception = 0;
    ID_dmem_read_o = 0;
    case (op)
      `OPCODE_LOAD:
      begin
        ID_dmem_read_o = 1;
        ID_reg_wr_en_o = `REGFILE_WRITE_ENABLE;
        ID_imm_src = `ID_I_ALU_TYPE_IMM_SRC;
        ID_alu_a_src_o = `ALU_A_SRC_SELECT_REG_DATA;
        ID_alu_b_src_o = `ALU_B_SRC_SELECT_IMM;
        ID_mem_wr_size_o = `MEM_NO_DMEM_WR;
        ID_result_src_o = `RESULT_SRC_SELECT_DMEM_RD_DATA;
        ID_branch_o = `IS_NOT_BRANCH_INSTR;
        ID_alu_op = `ALU_OP_ILOAD_S_U_TYPE;
        ID_jump_o = `IS_NOT_JUMP_INSTR;
        ID_pc_target_alu_src_o = `PC_TARGET_ALU_SRC_SELECT_PC;
        case(funct3)
          `FUNCT3_LB:
            ID_load_size_o = `DMEM_LOAD_SIZE_BYTE;
          `FUNCT3_LH:
            ID_load_size_o = `DMEM_LOAD_SIZE_HALF;
          `FUNCT3_LW:
            ID_load_size_o = `DMEM_LOAD_SIZE_WORD;
          `FUNCT3_LBU:
            ID_load_size_o = `DMEM_LOAD_SIZE_BYTEU;
          `FUNCT3_LHU:
            ID_load_size_o = `DMEM_LOAD_SIZE_HALFU;
          default:
          begin
            ID_load_size_o = `DMEM_LOAD_SIZE_NO_LOAD;
            opcode_exception = 1;
          end
        endcase
      end


      // ECALL should halt the cpu
      `OPCODE_ECALL:
      begin
        ID_reg_wr_en_o = `REGFILE_WRITE_DISABLE;
        //ID_alu_a_src_o = `ALU_A_SRC_SELECT_REG_DATA;
        //ID_alu_b_src_o = `ALU_B_SRC_SELECT_IMM;
        ID_mem_wr_size_o = `MEM_NO_DMEM_WR;
        //ID_result_src_o = `RESULT_SRC_SELECT_ALU_RESULT;
        ID_branch_o = `IS_NOT_BRANCH_INSTR;
        //ID_alu_op = `ALU_OP_IALU_ISHIFT_R_TYPE;
        ID_jump_o = `IS_NOT_JUMP_INSTR;
        ID_load_size_o = `DMEM_LOAD_SIZE_NO_LOAD;
        //ID_pc_target_alu_src_o = `PC_TARGET_ALU_SRC_SELECT_PC;
        //ID_imm_src = `ID_I_ALU_TYPE_IMM_SRC;
        //ID_is_nop = 0; 
        ID_is_ecall_o = 1;
      end
      //  ECALL should jump to the start

      `OPCODE_STORE:
      begin
        ID_reg_wr_en_o = `REGFILE_WRITE_DISABLE;
        ID_imm_src = `ID_S_TYPE_IMM_SRC;
        ID_alu_a_src_o = `ALU_A_SRC_SELECT_REG_DATA;
        ID_alu_b_src_o = `ALU_B_SRC_SELECT_IMM;
        ID_load_size_o = `DMEM_LOAD_SIZE_NO_LOAD;
        ID_result_src_o = `RESULT_SRC_NO_WRITEBACK;
        ID_branch_o = `IS_NOT_BRANCH_INSTR;
        ID_alu_op = `ALU_OP_ILOAD_S_U_TYPE;
        ID_jump_o = `IS_NOT_JUMP_INSTR;
        ID_pc_target_alu_src_o = `PC_TARGET_ALU_SRC_SELECT_PC;
        case(funct3)
          `FUNCT3_SB:
            ID_mem_wr_size_o = `MEM_BYTE_WR;	//sb
          `FUNCT3_SH:
            ID_mem_wr_size_o = `MEM_HALF_WR;	//sh
          `FUNCT3_SW:
            ID_mem_wr_size_o = `MEM_WORD_WR;	//sw
          default:
          begin
            ID_mem_wr_size_o = `MEM_NO_DMEM_WR;	//unknown instruction
            opcode_exception = 1;
          end
        endcase
      end
      `OPCODE_R_TYPE:
      begin
        ID_reg_wr_en_o = `REGFILE_WRITE_ENABLE;
        ID_imm_src = `ID_NO_IMM_SRC;
        ID_alu_a_src_o = `ALU_A_SRC_SELECT_REG_DATA;
        ID_alu_b_src_o = `ALU_B_SRC_SELECT_REG_DATA;
        ID_load_size_o = `DMEM_LOAD_SIZE_NO_LOAD;
        ID_result_src_o = `RESULT_SRC_SELECT_ALU_RESULT;
        ID_branch_o = `IS_NOT_BRANCH_INSTR;
        ID_alu_op = `ALU_OP_IALU_ISHIFT_R_TYPE;
        ID_jump_o = `IS_NOT_JUMP_INSTR;
        ID_pc_target_alu_src_o = `PC_TARGET_ALU_SRC_SELECT_PC;
        ID_mem_wr_size_o = `MEM_NO_DMEM_WR;
      end
      `OPCODE_B_TYPE:
      begin
        ID_reg_wr_en_o = `REGFILE_WRITE_DISABLE;
        ID_imm_src = `ID_B_TYPE_IMM_SRC;
        ID_alu_a_src_o = `ALU_A_SRC_SELECT_REG_DATA;
        ID_alu_b_src_o = `ALU_B_SRC_SELECT_REG_DATA;
        ID_mem_wr_size_o = `MEM_NO_DMEM_WR;
        ID_result_src_o = `RESULT_SRC_NO_WRITEBACK;
        ID_branch_o = `IS_BRANCH_INSTR;
        ID_alu_op = `ALU_OP_B_TYPE;
        ID_jump_o = `IS_NOT_JUMP_INSTR;
        ID_load_size_o = `DMEM_LOAD_SIZE_NO_LOAD;
        ID_pc_target_alu_src_o = `PC_TARGET_ALU_SRC_SELECT_PC;
      end
      //I-type ALU or shift
      `OPCODE_I_TYPE:
      begin
        ID_reg_wr_en_o = `REGFILE_WRITE_ENABLE;
        ID_alu_a_src_o = `ALU_A_SRC_SELECT_REG_DATA;
        ID_alu_b_src_o = `ALU_B_SRC_SELECT_IMM;
        ID_mem_wr_size_o = `MEM_NO_DMEM_WR;
        ID_result_src_o = `RESULT_SRC_SELECT_ALU_RESULT;
        ID_branch_o = `IS_NOT_BRANCH_INSTR;
        ID_alu_op = `ALU_OP_IALU_ISHIFT_R_TYPE;
        ID_jump_o = `IS_NOT_JUMP_INSTR;
        ID_load_size_o = `DMEM_LOAD_SIZE_NO_LOAD;
        ID_pc_target_alu_src_o = `PC_TARGET_ALU_SRC_SELECT_PC;
        case (funct3)
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
        ID_reg_wr_en_o = `REGFILE_WRITE_ENABLE;
        ID_imm_src = `ID_J_TYPE_IMM_SRC;
        ID_alu_a_src_o = `ALU_A_SRC_SELECT_REG_DATA;
        ID_alu_b_src_o = `ALU_B_SRC_SELECT_REG_DATA;
        ID_mem_wr_size_o = `MEM_NO_DMEM_WR;
        ID_result_src_o = `RESULT_SRC_SELECT_NEXT_INSTR_ADDR;
        ID_branch_o = `IS_NOT_BRANCH_INSTR;
        ID_alu_op = `ALU_OP_ILOAD_S_U_TYPE; // TODO
        ID_jump_o = `IS_JUMP_INSTR;
        ID_load_size_o = `DMEM_LOAD_SIZE_NO_LOAD;
        ID_pc_target_alu_src_o = `PC_TARGET_ALU_SRC_SELECT_PC;
      end

      `OPCODE_U_TYPE_LUI:
      begin
        ID_reg_wr_en_o = `REGFILE_WRITE_ENABLE;
        ID_imm_src = `ID_U_TYPE_IMM_SRC;
        ID_alu_a_src_o = `ALU_A_SRC_SELECT_ZERO;
        ID_alu_b_src_o = `ALU_B_SRC_SELECT_IMM;
        ID_mem_wr_size_o = `MEM_NO_DMEM_WR;
        ID_result_src_o = `RESULT_SRC_SELECT_ALU_RESULT;
        ID_branch_o = `IS_NOT_BRANCH_INSTR;
        ID_alu_op = `ALU_OP_ILOAD_S_U_TYPE;
        ID_jump_o = `IS_NOT_JUMP_INSTR;
        ID_load_size_o = `DMEM_LOAD_SIZE_NO_LOAD;
        ID_pc_target_alu_src_o = `PC_TARGET_ALU_SRC_SELECT_PC;
      end
      `OPCODE_U_TYPE_AUIPC:
      begin
        ID_reg_wr_en_o = `REGFILE_WRITE_ENABLE;
        ID_imm_src = `ID_U_TYPE_IMM_SRC;
        ID_alu_a_src_o = `ALU_A_SRC_SELECT_PC;
        ID_alu_b_src_o = `ALU_B_SRC_SELECT_IMM;
        ID_mem_wr_size_o = `MEM_NO_DMEM_WR;
        ID_result_src_o = `RESULT_SRC_SELECT_ALU_RESULT;
        ID_branch_o = `IS_NOT_BRANCH_INSTR;
        ID_alu_op = `ALU_OP_ILOAD_S_U_TYPE;
        ID_jump_o = `IS_NOT_JUMP_INSTR;
        ID_load_size_o = `DMEM_LOAD_SIZE_NO_LOAD;
        ID_pc_target_alu_src_o = `PC_TARGET_ALU_SRC_SELECT_PC;
      end
      `OPCODE_JALR:
      begin
        ID_reg_wr_en_o = `REGFILE_WRITE_ENABLE;
        ID_imm_src = `ID_I_ALU_TYPE_IMM_SRC;
        ID_alu_a_src_o = `ALU_A_SRC_SELECT_REG_DATA;
        ID_alu_b_src_o = `ALU_B_SRC_SELECT_IMM;
        ID_mem_wr_size_o = `MEM_NO_DMEM_WR;
        ID_result_src_o = `RESULT_SRC_SELECT_NEXT_INSTR_ADDR;
        ID_branch_o = `IS_NOT_BRANCH_INSTR;
        ID_alu_op = `ALU_OP_ILOAD_S_U_TYPE;
        ID_jump_o = `IS_JUMP_INSTR;
        ID_load_size_o = `DMEM_LOAD_SIZE_NO_LOAD;
        ID_pc_target_alu_src_o = `PC_TARGET_ALU_SRC_SELECT_REG_DATA;
      end
      default:
      begin
        ID_reg_wr_en_o = `REGFILE_WRITE_ENABLE;
        ID_alu_a_src_o = `ALU_A_SRC_SELECT_REG_DATA;
        ID_alu_b_src_o = `ALU_B_SRC_SELECT_IMM;
        ID_mem_wr_size_o = `MEM_NO_DMEM_WR;
        ID_result_src_o = `RESULT_SRC_SELECT_ALU_RESULT;
        ID_branch_o = `IS_NOT_BRANCH_INSTR;
        ID_alu_op = `ALU_OP_IALU_ISHIFT_R_TYPE;
        ID_jump_o = `IS_NOT_JUMP_INSTR;
        ID_load_size_o = `DMEM_LOAD_SIZE_NO_LOAD;
        ID_pc_target_alu_src_o = `PC_TARGET_ALU_SRC_SELECT_PC;	//unknown instruction default to i type
        ID_imm_src = `ID_I_ALU_TYPE_IMM_SRC; //I-type ALU
        opcode_exception = 1;
      end

    endcase

  end

  // decode the alu operation used for the instruction
  always_comb
  begin
    ID_alu_op_exception = 0;
    case (ID_alu_op)
      //I-type Load, S-type, U-type
      `ALU_OP_ILOAD_S_U_TYPE:
        ID_alu_control = `EX_ADD_ALU_CONTROL; //add- lw,sw,lb,lh,lbu,lhu,sb,sh,auipc,lui
      //B-type
      `ALU_OP_B_TYPE:
      case (funct3)
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
      case (funct3)
        `FUNCT3_ADD_SUB:
          ID_alu_control = (ID_r_type_sub) ? `EX_SUB_ALU_CONTROL /*sub*/ : `EX_ADD_ALU_CONTROL /*add*/;
        `FUNCT3_SLL:
          ID_alu_control = `EX_L_SHIFT_ALU_CONTROL; //sll
        `FUNCT3_SLT:
          ID_alu_control = `EX_LT_ALU_CONTROL; //slt
        `FUNCT3_SLTU_SLTIU:
          ID_alu_control = `EX_LTU_ALU_CONTROL; //sltu, sltiu
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
  
endmodule



