module decoder
  import params_pkg::*;
(

    input logic [6:0] OP,
    input [2:0] FUNCT3,
    input [6:0] FUNCT7,
    input logic [11:0] FUNCT12,
    input logic [4:0] RS1_ADDR,
    input logic [4:0] RD_ADDR,
    input logic RTYPE_ALT,
    input logic ITYPE_ALT,

    output logic RD_VALID,
    output logic RS1_VALID,
    output logic RS2_VALID,
    output mem_op_t MEM_OP,
    output cf_op_t CF_OP,
    output csr_op_t CSR_OP,
    output alu_control_t ALU_CONTROL,
    output imm_ext_op_t IMM_EXT_OP,
    output alu_a_sel_t ALU_A_SRC,
    output alu_b_sel_t ALU_B_SRC,
    output pc_alu_sel_t PC_ALU_SRC,
    output csr_bitmask_sel_t CSR_BITMASK_SEL,
    output logic [30:0] TRAP_MCAUSE,
    output logic TRAP_VALID
);

  logic rd_valid;
  logic rs1_valid;
  logic rs2_valid;
  mem_op_t mem_op;
  cf_op_t cf_op;
  csr_op_t csr_op;
  alu_control_t alu_control;
  imm_ext_op_t imm_ext_op;
  alu_a_sel_t alu_a_src;
  alu_b_sel_t alu_b_src;
  pc_alu_sel_t pc_alu_src;
  csr_bitmask_sel_t csr_bitmask_sel;

  alu_op_t alu_op;
  logic is_itype;
  logic is_rtype;
  logic is_SRAI_funct3;
  logic is_SRA_or_SUB_funct3;
  logic is_SLLI_or_SRLI_funct3;
  logic is_shift_itype;
  logic is_unknown_rtype;
  logic is_unknown_itype;

  assign is_itype = (OP == OPCODE_I_TYPE) ? 1 : 0;
  assign is_rtype = (OP == OPCODE_R_TYPE) ? 1 : 0;
  assign is_SRAI_funct3 = (FUNCT3 == FUNCT3_SRAI) ? 1 : 0;
  assign is_SRA_or_SUB_funct3 = ((FUNCT3 == FUNCT3_SRA) || (FUNCT3 == FUNCT3_SUB)) ? 1 : 0;
  assign is_SLLI_or_SRLI_funct3 = ((FUNCT3 == FUNCT3_SLLI) || (FUNCT3 == FUNCT3_SRLI)) ? 1 : 0;
  assign is_shift_itype = is_SLLI_or_SRLI_funct3 | is_SRAI_funct3;
  assign is_unknown_rtype          = is_rtype
    & (FUNCT7 != 7'h00)
    & ~((FUNCT7 == 7'h20) & is_SRA_or_SUB_funct3);
  assign is_unknown_itype = is_itype
    & is_shift_itype
    & ~(is_SLLI_or_SRLI_funct3 & (FUNCT7 == 7'h00))
    & ~(is_SRAI_funct3 & (FUNCT7 == 7'h20));


  // Decode the control signals for the specific instruction
  always_comb begin
    TRAP_VALID = 0;
    TRAP_MCAUSE = TRAP_CODE_ILLEGAL_INSTR;
    // valid registers
    rd_valid = 0;
    rs1_valid = 0;
    rs2_valid = 0;
    // ops
    alu_op = ALU_OP_ILOAD_S_U_TYPE;
    mem_op = MEM_NONE;
    cf_op = CF_NONE;
    csr_op = CSR_NONE;
    alu_op = ALU_OP_ILOAD_S_U_TYPE;
    // sources
    imm_ext_op = I_ALU_TYPE;
    alu_a_src = ALU_A_SEL_REG_DATA;
    alu_b_src = ALU_B_SEL_REG_DATA;
    pc_alu_src = PC_ALU_SEL_PC;
    csr_bitmask_sel = CSR_BITMASK_SEL_REG_DATA;


    case (OP)
      OPCODE_LOAD: begin
        rd_valid = 1;
        rs1_valid = 1;
        imm_ext_op = I_ALU_TYPE;
        alu_a_src = ALU_A_SEL_REG_DATA;
        alu_b_src = ALU_B_SEL_IMM;
        alu_op = ALU_OP_ILOAD_S_U_TYPE;
        pc_alu_src = PC_ALU_SEL_PC;
        case (FUNCT3)
          FUNCT3_LB:  mem_op = MEM_LB;
          FUNCT3_LH:  mem_op = MEM_LH;
          FUNCT3_LW:  mem_op = MEM_LW;
          FUNCT3_LBU: mem_op = MEM_LBU;
          FUNCT3_LHU: mem_op = MEM_LHU;
          default: begin
            TRAP_VALID  = 1;
            TRAP_MCAUSE = TRAP_CODE_ILLEGAL_INSTR;
          end
        endcase
      end

      OPCODE_SYSCALL_CSR: begin
        rs1_valid = 1;
        rd_valid  = 1;
        case (FUNCT3)
          FUNCT3_ECALL_EBREAK: begin
            TRAP_VALID = 1;
            if ((RS1_ADDR == 0) && (RD_ADDR == 0)) begin
              if (FUNCT12 == 12'h001) TRAP_MCAUSE = TRAP_CODE_BREAKPOINT;
              else if (FUNCT12 == 12'h000) TRAP_MCAUSE = TRAP_CODE_ECALL_M_MODE;
              else TRAP_MCAUSE = TRAP_CODE_ILLEGAL_INSTR;
            end else TRAP_MCAUSE = TRAP_CODE_ILLEGAL_INSTR;
          end
          FUNCT3_CSRRW: begin
            csr_op = CSR_WRITE;
            csr_bitmask_sel = CSR_BITMASK_SEL_REG_DATA;
          end
          FUNCT3_CSRRS: begin
            csr_op = (RS1_ADDR == 0) ? CSR_READ : CSR_SET;
            csr_bitmask_sel = CSR_BITMASK_SEL_REG_DATA;
          end
          FUNCT3_CSRRC: begin
            csr_op = (RS1_ADDR == 0) ? CSR_READ : CSR_CLEAR;
            csr_bitmask_sel = CSR_BITMASK_SEL_REG_DATA;
          end
          FUNCT3_CSRRWI: begin
            imm_ext_op = CSR_TYPE;
            csr_op = CSR_WRITE;
            csr_bitmask_sel = CSR_BITMASK_SEL_IMM;
          end
          FUNCT3_CSRRSI: begin
            imm_ext_op = CSR_TYPE;
            csr_op = (RS1_ADDR == 0) ? CSR_READ : CSR_SET;
            csr_bitmask_sel = CSR_BITMASK_SEL_IMM;
          end
          FUNCT3_CSRRCI: begin
            imm_ext_op = CSR_TYPE;
            csr_op = (RS1_ADDR == 0) ? CSR_READ : CSR_CLEAR;
            csr_bitmask_sel = CSR_BITMASK_SEL_IMM;
          end
          default: begin
            TRAP_VALID  = 1;
            TRAP_MCAUSE = TRAP_CODE_ILLEGAL_INSTR;
          end
        endcase
      end
      OPCODE_STORE: begin
        rs1_valid = 1;
        rs2_valid = 1;
        imm_ext_op = S_TYPE;
        alu_a_src = ALU_A_SEL_REG_DATA;
        alu_b_src = ALU_B_SEL_IMM;
        alu_op = ALU_OP_ILOAD_S_U_TYPE;
        pc_alu_src = PC_ALU_SEL_PC;
        case (FUNCT3)
          FUNCT3_SB: mem_op = MEM_SB;
          FUNCT3_SH: mem_op = MEM_SH;
          FUNCT3_SW: mem_op = MEM_SW;
          default: begin
            TRAP_VALID  = 1;
            TRAP_MCAUSE = TRAP_CODE_ILLEGAL_INSTR;
          end
        endcase
      end
      OPCODE_R_TYPE: begin
        if (is_unknown_rtype) begin
          TRAP_VALID  = 1;
          TRAP_MCAUSE = TRAP_CODE_ILLEGAL_INSTR;
        end else begin
          rs1_valid = 1;
          rs2_valid = 1;
          rd_valid = 1;
          alu_a_src = ALU_A_SEL_REG_DATA;
          alu_b_src = ALU_B_SEL_REG_DATA;
          alu_op = ALU_OP_IALU_ISHIFT_R_TYPE;
          pc_alu_src = PC_ALU_SEL_PC;
        end
      end
      OPCODE_B_TYPE: begin
        rs1_valid = 1;
        rs2_valid = 1;
        imm_ext_op = B_TYPE;
        alu_a_src = ALU_A_SEL_REG_DATA;
        alu_b_src = ALU_B_SEL_REG_DATA;
        cf_op = CF_BRANCH;
        alu_op = ALU_OP_B_TYPE;
        pc_alu_src = PC_ALU_SEL_PC;
      end
      //I-type ALU or shift
      OPCODE_I_TYPE: begin
        if (is_unknown_itype) begin
          TRAP_VALID  = 1;
          TRAP_MCAUSE = TRAP_CODE_ILLEGAL_INSTR;
        end else begin
          rs1_valid = 1;
          rd_valid = 1;
          alu_a_src = ALU_A_SEL_REG_DATA;
          alu_b_src = ALU_B_SEL_IMM;
          alu_op = ALU_OP_IALU_ISHIFT_R_TYPE;
          pc_alu_src = PC_ALU_SEL_PC;
          case (FUNCT3)
            3'b000, 3'b010, 3'b011, 3'b100, 3'b110, 3'b111: imm_ext_op = I_ALU_TYPE;  //I-type ALU
            3'b001, 3'b101: imm_ext_op = I_SHIFT_TYPE;  //I-type Shift
            default: begin
              TRAP_VALID  = 1;
              TRAP_MCAUSE = TRAP_CODE_ILLEGAL_INSTR;
            end
          endcase  //I-type shift
        end
      end
      OPCODE_JAL: begin
        rd_valid = 1;
        imm_ext_op = J_TYPE;
        alu_a_src = ALU_A_SEL_REG_DATA;
        alu_b_src = ALU_B_SEL_REG_DATA;
        alu_op = ALU_OP_ILOAD_S_U_TYPE;
        cf_op = CF_JUMP;
        pc_alu_src = PC_ALU_SEL_PC;
      end
      OPCODE_U_TYPE_LUI: begin
        rd_valid = 1;
        imm_ext_op = U_TYPE;
        alu_a_src = ALU_A_SEL_ZERO;
        alu_b_src = ALU_B_SEL_IMM;
        alu_op = ALU_OP_ILOAD_S_U_TYPE;
        pc_alu_src = PC_ALU_SEL_PC;
      end
      OPCODE_U_TYPE_AUIPC: begin
        rd_valid = 1;
        imm_ext_op = U_TYPE;
        alu_a_src = ALU_A_SEL_PC;
        alu_b_src = ALU_B_SEL_IMM;
        alu_op = ALU_OP_ILOAD_S_U_TYPE;
        pc_alu_src = PC_ALU_SEL_PC;
      end
      OPCODE_JALR: begin
        rs1_valid = 1;
        rd_valid = 1;
        imm_ext_op = I_ALU_TYPE;
        alu_a_src = ALU_A_SEL_REG_DATA;
        alu_b_src = ALU_B_SEL_IMM;
        alu_op = ALU_OP_ILOAD_S_U_TYPE;
        cf_op = CF_JALR;
        pc_alu_src = PC_ALU_SEL_REG_DATA;
      end
      default: begin
        TRAP_VALID  = 1;
        TRAP_MCAUSE = TRAP_CODE_ILLEGAL_INSTR;
      end
    endcase
  end



  always_comb begin
    alu_control = ADD_ALU_CONTROL;
    case (alu_op)
      //I-type Load, S-type, U-type
      ALU_OP_ILOAD_S_U_TYPE:
      alu_control = ADD_ALU_CONTROL;  //add- lw,sw,lb,lh,lbu,lhu,sb,sh,auipc,lui
      //B-type
      ALU_OP_B_TYPE:
      case (FUNCT3)
        FUNCT3_BEQ: alu_control = SUB_ALU_CONTROL;  //sub - beq
        FUNCT3_BNE: alu_control = NE_ALU_CONTROL;  //sub - bne
        FUNCT3_BLT: alu_control = LT_ALU_CONTROL;  //blt
        FUNCT3_BGE: alu_control = GE_ALU_CONTROL;  //bge
        FUNCT3_BLTU: alu_control = LTU_ALU_CONTROL;  //bltu
        FUNCT3_BGEU: alu_control = GEU_ALU_CONTROL;  //bgeu
        default: ;
      endcase
      //R-type, I-type ALU,I-type logical shift
      ALU_OP_IALU_ISHIFT_R_TYPE: begin
        case (FUNCT3)
          FUNCT3_ADD:
          alu_control = (RTYPE_ALT) ? SUB_ALU_CONTROL  /*sub*/ : ADD_ALU_CONTROL  /*add*/;
          FUNCT3_SLL: alu_control = L_SHIFT_ALU_CONTROL;  //sll
          FUNCT3_SLT: alu_control = LT_ALU_CONTROL;  //slt
          FUNCT3_SLTU_SLTIU: alu_control = LTU_ALU_CONTROL;  //sltu, sltiu
          FUNCT3_XOR: alu_control = XOR_ALU_CONTROL;  //xor
          FUNCT3_SRA:
          alu_control = (RTYPE_ALT || ITYPE_ALT) ? R_SHIFT_A_ALU_CONTROL /*sra*/ : R_SHIFT_L_ALU_CONTROL /*srl*/;
          FUNCT3_OR: alu_control = OR_ALU_CONTROL;  //or
          FUNCT3_AND: alu_control = AND_ALU_CONTROL;  //and
          default: ;
        endcase
      end
      default: ;
    endcase
  end

  assign RD_VALID = rd_valid;
  assign RS1_VALID = rs1_valid;
  assign RS2_VALID = rs2_valid;
  assign MEM_OP = mem_op;
  assign CF_OP = cf_op;
  assign CSR_OP = csr_op;
  assign ALU_CONTROL = alu_control;
  assign IMM_EXT_OP = imm_ext_op;
  assign ALU_A_SRC = alu_a_src;
  assign ALU_B_SRC = alu_b_src;
  assign PC_ALU_SRC = pc_alu_src;
  assign CSR_BITMASK_SEL = csr_bitmask_sel;

endmodule
