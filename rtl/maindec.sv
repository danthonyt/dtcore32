module maindec (
    input logic [6:0] op_i,
    input [2:0] funct3_i,
    input [6:0] funct7_i,
    input logic [11:0] funct12_i,
    input logic [4:0] rs1_addr_i,
    input logic [4:0] rd_addr_i,
    output logic valid_rd_addr_o,
    output logic valid_rs1_addr_o,
    output logic valid_rs2_addr_o,
    output logic [2:0] imm_src_o,
    output logic [1:0] alu_a_src_o,
    output logic alu_b_src_o,
    output logic [1:0] mem_stype_o,
    output logic [1:0] result_src_o,
    output logic branch_o,
    output logic [1:0] alu_op_o,
    output logic jump_o,
    output logic pc_target_alu_src_o,
    output logic [2:0] mem_ltype_o,
    output logic [1:0] csr_wtype_o,
    output logic csr_write_src_o,
    output logic is_jalr_o,
    output logic [30:0] trap_mcause_o,
    output logic trap_valid_o
);
  import params_pkg::*;
  logic is_itype;
  logic is_rtype;
  logic is_SRAI_funct3;
  logic is_SRA_or_SUB_funct3;
  logic is_SLLI_or_SRLI_funct3;
  logic is_shift_itype;
  logic is_unknown_rtype;
  logic is_unknown_itype;

  assign is_itype = (op_i == OPCODE_I_TYPE) ? 1 : 0;
  assign is_rtype = (op_i == OPCODE_R_TYPE) ? 1 : 0;
  assign is_SRAI_funct3 = (funct3_i == FUNCT3_SRAI) ? 1 : 0;
  assign is_SRA_or_SUB_funct3 = ((funct3_i == FUNCT3_SRA) || (funct3_i == FUNCT3_SUB)) ? 1 : 0;
  assign is_SLLI_or_SRLI_funct3 = ((funct3_i == FUNCT3_SLLI) || (funct3_i == FUNCT3_SRLI)) ? 1 : 0;
  assign is_shift_itype = is_SLLI_or_SRLI_funct3 | is_SRAI_funct3;
  assign is_unknown_rtype          = is_rtype
    & (funct7_i != 7'h00)
    & ~((funct7_i == 7'h20) & is_SRA_or_SUB_funct3);
  assign is_unknown_itype = is_itype
    & is_shift_itype
    & ~(is_SLLI_or_SRLI_funct3 & (funct7_i == 7'h00))
    & ~(is_SRAI_funct3 & (funct7_i == 7'h20));


  // Decode the control signals for the specific instruction
  always_comb begin
    valid_rd_addr_o = 0;
    valid_rs1_addr_o = 0;
    valid_rs2_addr_o = 0;
    trap_valid_o = 0;
    trap_mcause_o = TRAP_CODE_ILLEGAL_INSTR;
    // instructions should default to a nop
    imm_src_o = I_ALU_TYPE_IMM_SRC;
    alu_a_src_o = ALU_A_SRC_SELECT_REG_DATA;
    alu_b_src_o = ALU_B_SRC_SELECT_REG_DATA;
    mem_stype_o = MEM_NO_DMEM_WR;
    result_src_o = RESULT_SRC_SELECT_ALU_RESULT;
    branch_o = IS_NOT_BRANCH_INSTR;
    alu_op_o = ALU_OP_ILOAD_S_U_TYPE;
    jump_o = IS_NOT_JUMP_INSTR;
    pc_target_alu_src_o = PC_TARGET_ALU_SRC_SELECT_PC;
    mem_ltype_o = DMEM_LOAD_SIZE_NO_LOAD;
    csr_wtype_o = CSR_WRITE_DISABLE;
    csr_write_src_o = CSR_SRC_SELECT_REG_DATA;
    is_jalr_o = 0;
    case (op_i)
      OPCODE_LOAD: begin
        valid_rs1_addr_o = 1;
        valid_rd_addr_o = 1;
        imm_src_o = I_ALU_TYPE_IMM_SRC;
        alu_a_src_o = ALU_A_SRC_SELECT_REG_DATA;
        alu_b_src_o = ALU_B_SRC_SELECT_IMM;
        result_src_o = RESULT_SRC_SELECT_DMEM_RD_DATA;
        alu_op_o = ALU_OP_ILOAD_S_U_TYPE;
        pc_target_alu_src_o = PC_TARGET_ALU_SRC_SELECT_PC;
        case (funct3_i)
          FUNCT3_LB:  mem_ltype_o = DMEM_LOAD_SIZE_BYTE;
          FUNCT3_LH:  mem_ltype_o = DMEM_LOAD_SIZE_HALF;
          FUNCT3_LW:  mem_ltype_o = DMEM_LOAD_SIZE_WORD;
          FUNCT3_LBU: mem_ltype_o = DMEM_LOAD_SIZE_BYTEU;
          FUNCT3_LHU: mem_ltype_o = DMEM_LOAD_SIZE_HALFU;
          default: begin
            trap_valid_o  = 1;
            trap_mcause_o = TRAP_CODE_ILLEGAL_INSTR;
          end
        endcase
      end

      OPCODE_SYSCALL_CSR: begin
        valid_rs1_addr_o = 1;
        valid_rd_addr_o  = 1;
        case (funct3_i)
          FUNCT3_ECALL_EBREAK: begin
            trap_valid_o = 1;
            if ((rs1_addr_i == 0) && (rd_addr_i == 0)) begin
              if (funct12_i == 12'h001) trap_mcause_o = TRAP_CODE_BREAKPOINT;
              else if (funct12_i == 12'h000) trap_mcause_o = TRAP_CODE_ECALL_M_MODE;
              else trap_mcause_o = TRAP_CODE_ILLEGAL_INSTR;
            end else trap_mcause_o = TRAP_CODE_ILLEGAL_INSTR;
          end
          FUNCT3_CSRRW: begin
            result_src_o = RESULT_SRC_SELECT_CSR_READ_DATA;
            csr_wtype_o = CSR_WRITE_RAW_VALUE;
            csr_write_src_o = CSR_SRC_SELECT_REG_DATA;
          end
          FUNCT3_CSRRS: begin
            result_src_o = RESULT_SRC_SELECT_CSR_READ_DATA;
            csr_wtype_o = (rs1_addr_i == 0) ? CSR_WRITE_DISABLE : CSR_WRITE_SET_BIT_MASK;
            csr_write_src_o = CSR_SRC_SELECT_REG_DATA;
          end
          FUNCT3_CSRRC: begin
            result_src_o = RESULT_SRC_SELECT_CSR_READ_DATA;
            csr_wtype_o = (rs1_addr_i == 0) ? CSR_WRITE_DISABLE : CSR_WRITE_CLEAR_BIT_MASK;
            csr_write_src_o = CSR_SRC_SELECT_REG_DATA;
          end
          FUNCT3_CSRRWI: begin
            result_src_o = RESULT_SRC_SELECT_CSR_READ_DATA;
            imm_src_o = CSR_TYPE_IMM_SRC;
            csr_wtype_o = CSR_WRITE_RAW_VALUE;
            csr_write_src_o = CSR_SRC_SELECT_IMM;
          end
          FUNCT3_CSRRSI: begin
            result_src_o = RESULT_SRC_SELECT_CSR_READ_DATA;
            imm_src_o = CSR_TYPE_IMM_SRC;
            csr_wtype_o = (rs1_addr_i == 0) ? CSR_WRITE_DISABLE : CSR_WRITE_SET_BIT_MASK;
            csr_write_src_o = CSR_SRC_SELECT_IMM;
          end
          FUNCT3_CSRRCI: begin
            result_src_o = RESULT_SRC_SELECT_CSR_READ_DATA;
            imm_src_o = CSR_TYPE_IMM_SRC;
            csr_wtype_o = (rs1_addr_i == 0) ? CSR_WRITE_DISABLE : CSR_WRITE_CLEAR_BIT_MASK;
            csr_write_src_o = CSR_SRC_SELECT_IMM;
          end
          default: begin
            trap_valid_o  = 1;
            trap_mcause_o = TRAP_CODE_ILLEGAL_INSTR;
          end
        endcase
      end
      OPCODE_STORE: begin
        valid_rs1_addr_o = 1;
        valid_rs2_addr_o = 1;
        imm_src_o = S_TYPE_IMM_SRC;
        alu_a_src_o = ALU_A_SRC_SELECT_REG_DATA;
        alu_b_src_o = ALU_B_SRC_SELECT_IMM;
        alu_op_o = ALU_OP_ILOAD_S_U_TYPE;
        pc_target_alu_src_o = PC_TARGET_ALU_SRC_SELECT_PC;
        case (funct3_i)
          FUNCT3_SB: mem_stype_o = MEM_BYTE_WR;  //sb
          FUNCT3_SH: mem_stype_o = MEM_HALF_WR;  //sh
          FUNCT3_SW: mem_stype_o = MEM_WORD_WR;  //sw
          default: begin
            trap_valid_o  = 1;
            trap_mcause_o = TRAP_CODE_ILLEGAL_INSTR;
          end
        endcase
      end
      OPCODE_R_TYPE: begin
        if (is_unknown_rtype) begin
          trap_valid_o  = 1;
          trap_mcause_o = TRAP_CODE_ILLEGAL_INSTR;
        end else begin
          valid_rs1_addr_o = 1;
          valid_rs2_addr_o = 1;
          valid_rd_addr_o = 1;
          alu_a_src_o = ALU_A_SRC_SELECT_REG_DATA;
          alu_b_src_o = ALU_B_SRC_SELECT_REG_DATA;
          result_src_o = RESULT_SRC_SELECT_ALU_RESULT;
          alu_op_o = ALU_OP_IALU_ISHIFT_R_TYPE;
          pc_target_alu_src_o = PC_TARGET_ALU_SRC_SELECT_PC;
        end
      end
      OPCODE_B_TYPE: begin
        valid_rs1_addr_o = 1;
        valid_rs2_addr_o = 1;
        imm_src_o = B_TYPE_IMM_SRC;
        alu_a_src_o = ALU_A_SRC_SELECT_REG_DATA;
        alu_b_src_o = ALU_B_SRC_SELECT_REG_DATA;
        branch_o = IS_BRANCH_INSTR;
        alu_op_o = ALU_OP_B_TYPE;
        pc_target_alu_src_o = PC_TARGET_ALU_SRC_SELECT_PC;
      end
      //I-type ALU or shift
      OPCODE_I_TYPE: begin
        if (is_unknown_itype) begin
          trap_valid_o  = 1;
          trap_mcause_o = TRAP_CODE_ILLEGAL_INSTR;
        end else begin
          valid_rs1_addr_o = 1;
          valid_rd_addr_o = 1;
          alu_a_src_o = ALU_A_SRC_SELECT_REG_DATA;
          alu_b_src_o = ALU_B_SRC_SELECT_IMM;
          result_src_o = RESULT_SRC_SELECT_ALU_RESULT;
          alu_op_o = ALU_OP_IALU_ISHIFT_R_TYPE;
          pc_target_alu_src_o = PC_TARGET_ALU_SRC_SELECT_PC;
          case (funct3_i)
            3'b000, 3'b010, 3'b011, 3'b100, 3'b110, 3'b111:
            imm_src_o = I_ALU_TYPE_IMM_SRC;  //I-type ALU
            3'b001, 3'b101: imm_src_o = I_SHIFT_TYPE_IMM_SRC;  //I-type Shift
            default: begin
              trap_valid_o  = 1;
              trap_mcause_o = TRAP_CODE_ILLEGAL_INSTR;
            end
          endcase  //I-type shift
        end
      end
      OPCODE_JAL: begin
        valid_rd_addr_o = 1;
        imm_src_o = J_TYPE_IMM_SRC;
        alu_a_src_o = ALU_A_SRC_SELECT_REG_DATA;
        alu_b_src_o = ALU_B_SRC_SELECT_REG_DATA;
        result_src_o = RESULT_SRC_SELECT_NEXT_INSTR_ADDR;
        alu_op_o = ALU_OP_ILOAD_S_U_TYPE;
        jump_o = IS_JUMP_INSTR;
        pc_target_alu_src_o = PC_TARGET_ALU_SRC_SELECT_PC;
      end
      OPCODE_U_TYPE_LUI: begin
        valid_rd_addr_o = 1;
        imm_src_o = U_TYPE_IMM_SRC;
        alu_a_src_o = ALU_A_SRC_SELECT_ZERO;
        alu_b_src_o = ALU_B_SRC_SELECT_IMM;
        result_src_o = RESULT_SRC_SELECT_ALU_RESULT;
        alu_op_o = ALU_OP_ILOAD_S_U_TYPE;
        pc_target_alu_src_o = PC_TARGET_ALU_SRC_SELECT_PC;
      end
      OPCODE_U_TYPE_AUIPC: begin
        valid_rd_addr_o = 1;
        imm_src_o = U_TYPE_IMM_SRC;
        alu_a_src_o = ALU_A_SRC_SELECT_PC;
        alu_b_src_o = ALU_B_SRC_SELECT_IMM;
        result_src_o = RESULT_SRC_SELECT_ALU_RESULT;
        alu_op_o = ALU_OP_ILOAD_S_U_TYPE;
        pc_target_alu_src_o = PC_TARGET_ALU_SRC_SELECT_PC;
      end
      OPCODE_JALR: begin
        valid_rs1_addr_o = 1;
        valid_rd_addr_o = 1;
        imm_src_o = I_ALU_TYPE_IMM_SRC;
        alu_a_src_o = ALU_A_SRC_SELECT_REG_DATA;
        alu_b_src_o = ALU_B_SRC_SELECT_IMM;
        result_src_o = RESULT_SRC_SELECT_NEXT_INSTR_ADDR;
        alu_op_o = ALU_OP_ILOAD_S_U_TYPE;
        jump_o = IS_JUMP_INSTR;
        pc_target_alu_src_o = PC_TARGET_ALU_SRC_SELECT_REG_DATA;
        is_jalr_o = 1;
      end
      default: begin
        trap_valid_o  = 1;
        trap_mcause_o = TRAP_CODE_ILLEGAL_INSTR;
      end
    endcase
  end
endmodule
