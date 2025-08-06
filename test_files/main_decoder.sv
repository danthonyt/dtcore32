module main_decoder
  import params_pkg::*;
(
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
  output logic [30:0] main_decoder_trap_code_o,
  output logic main_decoder_trap_valid_o
);


  logic valid_rd_addr;
  logic valid_rs1_addr;
  logic valid_rs2_addr;
  logic [2:0] imm_src;
  logic [1:0] alu_a_src;
  logic alu_b_src;
  logic [1:0] mem_stype;
  logic [1:0] result_src;
  logic branch;
  logic [6:0] alu_op;
  logic jump;
  logic pc_target_alu_src;
  logic [2:0] mem_ltype;
  logic [1:0] csr_wtype;
  logic csr_write_src;
  logic [30:0] main_decoder_trap_code;
  logic main_decoder_trap_valid;

    // unknown instruction finding logic
  logic is_SRAI_funct3;
  logic is_SRA_or_SUB_funct3;
  logic is_SLLI_or_SRLI_funct3;
  logic is_unknown_ishift;
  logic is_unknown_rtype;

  // logic for determining an unknown ishift and rtype instruction
  assign is_SRAI_funct3         = (funct3_i == FUNCT3_SRAI) ? 1 : 0;
  assign is_SRA_or_SUB_funct3   = ((funct3_i == FUNCT3_SRA) || (funct3_i == FUNCT3_SUB)) ? 1 : 0;
  assign is_SLLI_or_SRLI_funct3 = ((funct3_i == FUNCT3_SLLI) || (funct3_i == FUNCT3_SRLI)) ? 1 : 0;
  assign is_unknown_rtype       = (funct7_i != 7'h00) & ~((funct7_i == 7'h20) & is_SRA_or_SUB_funct3);
  assign is_unknown_ishift      = ~(is_SLLI_or_SRLI_funct3 & (funct7_i == 7'h00)) & ~(is_SRAI_funct3 & (funct7_i == 7'h20));

  // Decode the control signals for the specific instruction
  always_comb begin
    valid_rd_addr = 0;
    valid_rs1_addr = 0;
    valid_rs2_addr = 0;
    main_decoder_trap_valid = 1;
    main_decoder_trap_code = TRAP_CODE_ILLEGAL_INSTR;
    // instructions should default to a nop
    imm_src = I_ALU_TYPE_IMM_SRC;
    alu_a_src = ALU_A_SRC_SELECT_REG_DATA;
    alu_b_src = ALU_B_SRC_SELECT_REG_DATA;
    mem_stype = MEM_NO_DMEM_WR;
    result_src = RESULT_SRC_SELECT_ALU_RESULT;
    branch = IS_NOT_BRANCH_INSTR;
    alu_op = ALU_OP_ILOAD_S_U_TYPE;
    jump = IS_NOT_JUMP_INSTR;
    pc_target_alu_src = PC_TARGET_ALU_SRC_SELECT_PC;
    mem_ltype = DMEM_LOAD_SIZE_NO_LOAD;
    csr_wtype = CSR_WRITE_DISABLE;
    csr_write_src = CSR_SRC_SELECT_REG_DATA;
    // keep nop values if decode stage is a trap
    case (op_i)
      OPCODE_LOAD: begin
        main_decoder_trap_valid = 0;
        valid_rs1_addr = 1;
        valid_rd_addr = 1;
        imm_src = I_ALU_TYPE_IMM_SRC;
        alu_a_src = ALU_A_SRC_SELECT_REG_DATA;
        alu_b_src = ALU_B_SRC_SELECT_IMM;
        result_src = RESULT_SRC_SELECT_DMEM_RD_DATA;
        alu_op = ALU_OP_ILOAD_S_U_TYPE;
        pc_target_alu_src = PC_TARGET_ALU_SRC_SELECT_PC;
        case (funct3_i)
          FUNCT3_LB: mem_ltype = DMEM_LOAD_SIZE_BYTE;
          FUNCT3_LH: mem_ltype = DMEM_LOAD_SIZE_HALF;
          FUNCT3_LW: mem_ltype = DMEM_LOAD_SIZE_WORD;
          FUNCT3_LBU: mem_ltype = DMEM_LOAD_SIZE_BYTEU;
          FUNCT3_LHU: mem_ltype = DMEM_LOAD_SIZE_HALFU;
          default: main_decoder_trap_valid = 1;
        endcase
      end

      OPCODE_SYSCALL_CSR: begin
        valid_rs1_addr = 1;
        valid_rd_addr  = 1;
        case (funct3_i)
          FUNCT3_ECALL_EBREAK: begin
            main_decoder_trap_valid = 1;
            if ((ID_rs1_addr == 0) && (ID_rd_addr == 0)) begin
              if (ID_funct12 == 12'h001)  main_decoder_trap_code = TRAP_CODE_BREAKPOINT;
              else if (ID_funct12 == 12'h000) main_decoder_trap_code = TRAP_CODE_ECALL_M_MODE;
              else main_decoder_trap_code = TRAP_CODE_ILLEGAL_INSTR;
            end
            else main_decoder_trap_code = TRAP_CODE_ILLEGAL_INSTR;
          end
          FUNCT3_CSRRW: begin
            main_decoder_trap_valid = 0;
            result_src = RESULT_SRC_SELECT_CSR_READ_DATA;
            csr_wtype = CSR_WRITE_RAW_VALUE;
            csr_write_src = CSR_SRC_SELECT_REG_DATA;
          end
          FUNCT3_CSRRS: begin
            main_decoder_trap_valid = 0;
            result_src = RESULT_SRC_SELECT_CSR_READ_DATA;
            csr_wtype = (rs1_addr_i == 0) ? CSR_WRITE_DISABLE : CSR_WRITE_SET_BIT_MASK;
            csr_write_src = CSR_SRC_SELECT_REG_DATA;
          end
          FUNCT3_CSRRC: begin
            main_decoder_trap_valid = 0;
            result_src = RESULT_SRC_SELECT_CSR_READ_DATA;
            csr_wtype = (rs1_addr_i == 0) ? CSR_WRITE_DISABLE : CSR_WRITE_CLEAR_BIT_MASK;
            csr_write_src = CSR_SRC_SELECT_REG_DATA;
          end
          FUNCT3_CSRRWI: begin
            main_decoder_trap_valid = 0;
            result_src = RESULT_SRC_SELECT_CSR_READ_DATA;
            imm_src = CSR_TYPE_IMM_SRC;
            csr_wtype = CSR_WRITE_RAW_VALUE;
            csr_write_src = CSR_SRC_SELECT_IMM;
          end
          FUNCT3_CSRRSI: begin
            main_decoder_trap_valid = 0;
            result_src = RESULT_SRC_SELECT_CSR_READ_DATA;
            imm_src = CSR_TYPE_IMM_SRC;
            csr_wtype = (rs1_addr_i == 0) ? CSR_WRITE_DISABLE : CSR_WRITE_SET_BIT_MASK;
            csr_write_src = CSR_SRC_SELECT_IMM;
          end
          FUNCT3_CSRRCI: begin
            main_decoder_trap_valid = 0;
            result_src = RESULT_SRC_SELECT_CSR_READ_DATA;
            imm_src = CSR_TYPE_IMM_SRC;
            csr_wtype = (rs1_addr_i == 0) ? CSR_WRITE_DISABLE : CSR_WRITE_CLEAR_BIT_MASK;
            csr_write_src = CSR_SRC_SELECT_IMM;
          end
          default: ;
        endcase
      end
      OPCODE_STORE: begin
        valid_rs1_addr = 1;
        valid_rs2_addr = 1;
        main_decoder_trap_valid = 0;
        imm_src = S_TYPE_IMM_SRC;
        alu_a_src = ALU_A_SRC_SELECT_REG_DATA;
        alu_b_src = ALU_B_SRC_SELECT_IMM;
        alu_op = ALU_OP_ILOAD_S_U_TYPE;
        pc_target_alu_src = PC_TARGET_ALU_SRC_SELECT_PC;
        case (funct3_i)
          FUNCT3_SB: mem_stype = MEM_BYTE_WR;  //sb
          FUNCT3_SH: mem_stype = MEM_HALF_WR;  //sh
          FUNCT3_SW: mem_stype = MEM_WORD_WR;  //sw
          default:   main_decoder_trap_valid = 1;
        endcase
      end
      OPCODE_R_TYPE: begin
        if (is_unknown_rtype) begin
          main_decoder_trap_valid = 1;
          main_decoder_trap_code = TRAP_CODE_ILLEGAL_INSTR;
        end else begin
          main_decoder_trap_valid = 0;
          valid_rs1_addr = 1;
          valid_rs2_addr = 1;
          valid_rd_addr = 1;
          alu_a_src = ALU_A_SRC_SELECT_REG_DATA;
          alu_b_src = ALU_B_SRC_SELECT_REG_DATA;
          result_src = RESULT_SRC_SELECT_ALU_RESULT;
          alu_op = ALU_OP_IALU_ISHIFT_R_TYPE;
          pc_target_alu_src = PC_TARGET_ALU_SRC_SELECT_PC;
        end
      end
      OPCODE_B_TYPE: begin
        valid_rs1_addr = 1;
        valid_rs2_addr = 1;
        main_decoder_trap_valid = 0;
        imm_src = B_TYPE_IMM_SRC;
        alu_a_src = ALU_A_SRC_SELECT_REG_DATA;
        alu_b_src = ALU_B_SRC_SELECT_REG_DATA;
        branch = IS_BRANCH_INSTR;
        alu_op = ALU_OP_B_TYPE;
        pc_target_alu_src = PC_TARGET_ALU_SRC_SELECT_PC;
      end
      //I-type ALU or shift
      OPCODE_I_TYPE: begin
        if (is_unknown_ishift) begin
          main_decoder_trap_valid = 1;
          main_decoder_trap_code = TRAP_CODE_ILLEGAL_INSTR;
        end else begin
          valid_rs1_addr = 1;
          valid_rd_addr = 1;
          main_decoder_trap_valid = 0;
          alu_a_src = ALU_A_SRC_SELECT_REG_DATA;
          alu_b_src = ALU_B_SRC_SELECT_IMM;
          result_src = RESULT_SRC_SELECT_ALU_RESULT;
          alu_op = ALU_OP_IALU_ISHIFT_R_TYPE;
          pc_target_alu_src = PC_TARGET_ALU_SRC_SELECT_PC;
          case (funct3_i)
            3'b000, 3'b010, 3'b011, 3'b100, 3'b110, 3'b111:
              imm_src = I_ALU_TYPE_IMM_SRC;  //I-type ALU
            FUNCT3_SRAI, FUNCT3_SLLI: imm_src = I_SHIFT_TYPE_IMM_SRC;  //I-type Shift
            default: main_decoder_trap_valid = 1;
          endcase  //I-type shift
        end
      end
      OPCODE_JAL: begin
        valid_rd_addr = 1;
        main_decoder_trap_valid = 0;
        imm_src = J_TYPE_IMM_SRC;
        alu_a_src = ALU_A_SRC_SELECT_REG_DATA;
        alu_b_src = ALU_B_SRC_SELECT_REG_DATA;
        result_src = RESULT_SRC_SELECT_NEXT_INSTR_ADDR;
        alu_op = ALU_OP_ILOAD_S_U_TYPE;
        jump = IS_JUMP_INSTR;
        pc_target_alu_src = PC_TARGET_ALU_SRC_SELECT_PC;
      end
      OPCODE_U_TYPE_LUI: begin
        valid_rd_addr = 1;
        main_decoder_trap_valid = 0;
        imm_src = U_TYPE_IMM_SRC;
        alu_a_src = ALU_A_SRC_SELECT_ZERO;
        alu_b_src = ALU_B_SRC_SELECT_IMM;
        result_src = RESULT_SRC_SELECT_ALU_RESULT;
        alu_op = ALU_OP_ILOAD_S_U_TYPE;
        pc_target_alu_src = PC_TARGET_ALU_SRC_SELECT_PC;
      end
      OPCODE_U_TYPE_AUIPC: begin
        valid_rd_addr = 1;
        main_decoder_trap_valid = 0;
        imm_src = U_TYPE_IMM_SRC;
        alu_a_src = ALU_A_SRC_SELECT_PC;
        alu_b_src = ALU_B_SRC_SELECT_IMM;
        result_src = RESULT_SRC_SELECT_ALU_RESULT;
        alu_op = ALU_OP_ILOAD_S_U_TYPE;
        pc_target_alu_src = PC_TARGET_ALU_SRC_SELECT_PC;
      end
      OPCODE_JALR: begin
        valid_rs1_addr = 1;
        valid_rd_addr = 1;
        main_decoder_trap_valid = 0;
        imm_src = I_ALU_TYPE_IMM_SRC;
        alu_a_src = ALU_A_SRC_SELECT_REG_DATA;
        alu_b_src = ALU_B_SRC_SELECT_IMM;
        result_src = RESULT_SRC_SELECT_NEXT_INSTR_ADDR;
        alu_op = ALU_OP_ILOAD_S_U_TYPE;
        jump = IS_JUMP_INSTR;
        pc_target_alu_src = PC_TARGET_ALU_SRC_SELECT_REG_DATA;
      end
      default: main_decoder_trap_valid = 1;
    endcase
  end

  always_comb begin
    valid_rd_addr_o = valid_rd_addr;
    valid_rs1_addr_o = valid_rs1_addr;
    valid_rs2_addr_o = valid_rs2_addr;
    imm_src_o = imm_src;
    alu_a_src_o = alu_a_src;
    alu_b_src_o = alu_b_src;
    mem_stype_o = mem_stype;
    result_src_o = result_src;
    branch_o = branch;
    alu_op_o = alu_op;
    jump_o = jump;
    pc_target_alu_src_o = pc_target_alu_src;
    mem_ltype_o = mem_ltype;
    csr_wtype_o = csr_wtype;
    csr_write_src_o = csr_write_src;
    main_decoder_trap_code_o = main_decoder_trap_code;
    main_decoder_trap_valid_o = main_decoder_trap_valid;
  end
endmodule
