
//ID_reg_wr
`define REGFILE_WRITE_DISABLE 1'b0
`define REGFILE_WRITE_ENABLE 1'b1

//ID_imm_src
`define ID_NO_IMM_SRC 3'b000
`define ID_I_ALU_TYPE_IMM_SRC 3'b000
`define ID_S_TYPE_IMM_SRC 3'b001
`define ID_B_TYPE_IMM_SRC 3'b010
`define ID_J_TYPE_IMM_SRC 3'b011
`define ID_I_SHIFT_TYPE_IMM_SRC 3'b100
`define ID_U_TYPE_IMM_SRC 3'b101

//ID_alu_a_src
`define ALU_A_SRC_SELECT_REG_DATA 2'b00
`define ALU_A_SRC_SELECT_ZERO 2'b01
`define ALU_A_SRC_SELECT_PC 2'b10

//ID_alu_b_src
`define ALU_B_SRC_SELECT_REG_DATA 1'b0
`define ALU_B_SRC_SELECT_IMM 1'b1


//ID_mem_wr
`define MEM_NO_DMEM_WR 2'b00
`define MEM_WORD_WR 2'b01
`define MEM_HALF_WR 2'b10
`define MEM_BYTE_WR 2'b11

//ID_result_src
`define RESULT_SRC_NO_WRITEBACK 2'b00
`define RESULT_SRC_SELECT_ALU_RESULT 2'b00
`define RESULT_SRC_SELECT_DMEM_RD_DATA 2'b01
`define RESULT_SRC_SELECT_NEXT_INSTR_ADDR 2'b10

//ID_branch
`define IS_BRANCH_INSTR 1'b1
`define IS_NOT_BRANCH_INSTR 1'b0

//ID_alu_op
`define ALU_OP_ILOAD_S_U_TYPE 2'b00
`define ALU_OP_B_TYPE 2'b01
`define ALU_OP_IALU_ISHIFT_R_TYPE 2'b10

//ID_jump
`define IS_JUMP_INSTR 1'b1
`define IS_NOT_JUMP_INSTR 1'b0

//ID_load_size
`define DMEM_LOAD_SIZE_NO_LOAD 3'b000
`define DMEM_LOAD_SIZE_WORD 3'b000
`define DMEM_LOAD_SIZE_HALF 3'b011
`define DMEM_LOAD_SIZE_HALFU 3'b100
`define DMEM_LOAD_SIZE_BYTE 3'b001
`define DMEM_LOAD_SIZE_BYTEU 3'b010

//ID_pc_target_alu_src
`define PC_TARGET_ALU_SRC_SELECT_PC 1'b0
`define PC_TARGET_ALU_SRC_SELECT_REG_DATA 1'b1

// OPCODES
`define OPCODE_LOAD 7'b0000011
`define OPCODE_STORE 7'b0100011
`define OPCODE_R_TYPE 7'b0110011
`define OPCODE_B_TYPE 7'b1100011
`define OPCODE_I_TYPE 7'b0010011
`define OPCODE_JAL 7'b1101111
`define OPCODE_U_TYPE_LUI 7'b0110111
`define OPCODE_U_TYPE_AUIPC 7'b0010111
`define OPCODE_JALR 7'b1100111
`define OPCODE_SYSTEM 7'b1110011
`define OPCODE_FENCE 7'b00001111
// FUNCT3
`define FUNCT3_LB 3'b000
`define FUNCT3_LH 3'b001
`define FUNCT3_LW 3'b010
`define FUNCT3_LBU 3'b100
`define FUNCT3_LHU 3'b101

`define FUNCT3_SB 3'b000
`define FUNCT3_SH 3'b001
`define FUNCT3_SW 3'b010

`define FUNCT3_BEQ 3'b000
`define FUNCT3_BNE 3'b001
`define FUNCT3_BLT 3'b100
`define FUNCT3_BGE 3'b101
`define FUNCT3_BLTU  3'b110
`define FUNCT3_BGEU 3'b111

`define FUNCT3_ADD_SUB 3'b000
`define FUNCT3_SLL 3'b001
`define FUNCT3_SLT 3'b010
`define FUNCT3_SLTU 3'b011
`define FUNCT3_XOR 3'b100
`define FUNCT3_SRA_SRL 3'b101
`define FUNCT3_OR 3'b110
`define FUNCT3_AND 3'b111

`define FUNCT3_ECALL_EBREAK 3'b000

//alu module control
`define EX_ADD_ALU_CONTROL 4'h0
`define EX_SUB_ALU_CONTROL 4'h1
`define EX_AND_ALU_CONTROL 4'h2
`define EX_OR_ALU_CONTROL 4'h3
`define EX_L_SHIFT_ALU_CONTROL 4'h4
`define EX_LT_ALU_CONTROL 4'h5
`define EX_LTU_ALU_CONTROL 4'h6
`define EX_XOR_ALU_CONTROL 4'h7
`define EX_R_SHIFT_A_ALU_CONTROL 4'h8
`define EX_R_SHIFT_L_ALU_CONTROL 4'h9
`define EX_BNE_ALU_CONTROL 4'hC
`define EX_GE_ALU_CONTROL 4'hA
`define EX_GEU_ALU_CONTROL 4'hB
`define EX_NE_ALU_CONTROL 4'hC


module dtcore32_controller(
    input logic clk,rst,
    input logic [6:0]  op,
    input logic [2:0]  funct3,
    input logic funct7b5,
    output logic [1:0]  ID_result_src_o,
    output logic [1:0]  ID_alu_a_src_o,
    output logic [1:0]  ID_mem_wr_o,
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
  logic [1:0]  ID_mem_wr;
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


  assign ID_r_type_sub = op[5] & funct7b5;
  assign ID_i_type_sub = ~op[5] & funct7b5;
  
  

  // exception handling
  always_ff @(posedge clk)
  begin
    if (rst)
      ID_exception <=0;
    else
      ID_exception <= opcode_exception | ID_alu_op_exception;
  end
  always_comb
  begin
    ID_is_nop = 0;
    opcode_exception = 0;
    case (op)
      `OPCODE_LOAD:
      begin
        ID_reg_wr = `REGFILE_WRITE_ENABLE;
        ID_imm_src = `ID_I_ALU_TYPE_IMM_SRC;
        ID_alu_a_src = `ALU_A_SRC_SELECT_REG_DATA;
        ID_alu_b_src = `ALU_B_SRC_SELECT_IMM;
        ID_mem_wr = `MEM_NO_DMEM_WR;
        ID_result_src = `RESULT_SRC_SELECT_DMEM_RD_DATA;
        ID_branch = `IS_NOT_BRANCH_INSTR;
        ID_alu_op = `ALU_OP_ILOAD_S_U_TYPE;
        ID_jump = `IS_NOT_JUMP_INSTR;
        ID_pc_target_alu_src = `PC_TARGET_ALU_SRC_SELECT_PC;
        case(funct3)
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
        ID_mem_wr = `MEM_NO_DMEM_WR;
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
        case(funct3)
          `FUNCT3_SB:
            ID_mem_wr = `MEM_BYTE_WR;	//sb
          `FUNCT3_SH:
            ID_mem_wr = `MEM_HALF_WR;	//sh
          `FUNCT3_SW:
            ID_mem_wr = `MEM_WORD_WR;	//sw
          default:
          begin
            ID_mem_wr = `MEM_NO_DMEM_WR;	//unknown instruction
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
        ID_mem_wr = `MEM_NO_DMEM_WR;
      end
      `OPCODE_B_TYPE:
      begin
        ID_reg_wr = `REGFILE_WRITE_DISABLE;
        ID_imm_src = `ID_B_TYPE_IMM_SRC;
        ID_alu_a_src = `ALU_A_SRC_SELECT_REG_DATA;
        ID_alu_b_src = `ALU_B_SRC_SELECT_REG_DATA;
        ID_mem_wr = `MEM_NO_DMEM_WR;
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
        ID_mem_wr = `MEM_NO_DMEM_WR;
        ID_result_src = `RESULT_SRC_SELECT_ALU_RESULT;
        ID_branch = `IS_NOT_BRANCH_INSTR;
        ID_alu_op = `ALU_OP_IALU_ISHIFT_R_TYPE;
        ID_jump = `IS_NOT_JUMP_INSTR;
        ID_load_size = `DMEM_LOAD_SIZE_NO_LOAD;
        ID_pc_target_alu_src = `PC_TARGET_ALU_SRC_SELECT_PC;
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
        ID_reg_wr = `REGFILE_WRITE_ENABLE;
        ID_imm_src = `ID_J_TYPE_IMM_SRC;
        ID_alu_a_src = `ALU_A_SRC_SELECT_REG_DATA;
        ID_alu_b_src = `ALU_B_SRC_SELECT_REG_DATA;
        ID_mem_wr = `MEM_NO_DMEM_WR;
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
        ID_mem_wr = `MEM_NO_DMEM_WR;
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
        ID_mem_wr = `MEM_NO_DMEM_WR;
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
        ID_mem_wr = `MEM_NO_DMEM_WR;
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
        ID_mem_wr = `MEM_NO_DMEM_WR;
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
  assign ID_mem_wr_o = ID_mem_wr;
  assign ID_imm_src_o = ID_imm_src;
  assign ID_load_size_o = ID_load_size;
  assign ID_alu_b_src_o = ID_alu_b_src;
  assign ID_reg_wr_o = ID_reg_wr;
  assign ID_jump_o = ID_jump;
  assign ID_branch_o = ID_branch;
  assign ID_pc_target_alu_src_o = ID_pc_target_alu_src;

endmodule



