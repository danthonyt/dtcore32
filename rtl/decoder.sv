module decoder
  import params_pkg::*;
(

    input logic [6:0] op_i,
    input [2:0] funct3_i,
    input [6:0] funct7_i,
    input logic [11:0] funct12_i,
    input logic [4:0] rs1_addr_i,
    input logic [4:0] rd_addr_i,
    input logic rtype_alt_i,
    input logic itype_alt_i,

    output logic rd_valid_o,
    output logic rs1_valid_o,
    output logic rs2_valid_o,
    output mem_op_t mem_op_o,
    output cf_op_t cf_op_o,
    output csr_op_t csr_op_o,
    output alu_control_t alu_control_o,
    output imm_ext_op_t imm_ext_op_o,
    output alu_a_sel_t alu_a_sel_o,
    output alu_b_sel_t alu_b_sel_o,
    output pc_alu_sel_t pc_alu_sel_o,
    output csr_bitmask_sel_t csr_bitmask_sel_o,
    output logic illegal_instr_trap_o,
    output logic ecall_m_trap_o,
    output logic breakpoint_trap_o
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
    ecall_m_trap_o = 0;
    illegal_instr_trap_o = 0;
    breakpoint_trap_o = 0;
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


    case (op_i)
      OPCODE_LOAD: begin
        rd_valid = 1;
        rs1_valid = 1;
        imm_ext_op = I_ALU_TYPE;
        alu_a_src = ALU_A_SEL_REG_DATA;
        alu_b_src = ALU_B_SEL_IMM;
        alu_op = ALU_OP_ILOAD_S_U_TYPE;
        pc_alu_src = PC_ALU_SEL_PC;
        case (funct3_i)
          FUNCT3_LB:  mem_op = MEM_LB;
          FUNCT3_LH:  mem_op = MEM_LH;
          FUNCT3_LW:  mem_op = MEM_LW;
          FUNCT3_LBU: mem_op = MEM_LBU;
          FUNCT3_LHU: mem_op = MEM_LHU;
          default: begin
            illegal_instr_trap_o = 1;
          end
        endcase
      end

      OPCODE_SYSCALL_CSR: begin
        rs1_valid = 1;
        rd_valid  = 1;
        case (funct3_i)
          FUNCT3_ECALL_EBREAK: begin
            if ((rs1_addr_i == 0) && (rd_addr_i == 0)) begin
              if (funct12_i == 12'h001) breakpoint_trap_o = 1;
              else if (funct12_i == 12'h000) ecall_m_trap_o = 1;
              else illegal_instr_trap_o = 1;
            end else illegal_instr_trap_o = 1;
          end
          FUNCT3_CSRRW: begin
            csr_op = CSR_WRITE;
            csr_bitmask_sel = CSR_BITMASK_SEL_REG_DATA;
          end
          FUNCT3_CSRRS: begin
            csr_op = (rs1_addr_i == 0) ? CSR_READ : CSR_SET;
            csr_bitmask_sel = CSR_BITMASK_SEL_REG_DATA;
          end
          FUNCT3_CSRRC: begin
            csr_op = (rs1_addr_i == 0) ? CSR_READ : CSR_CLEAR;
            csr_bitmask_sel = CSR_BITMASK_SEL_REG_DATA;
          end
          FUNCT3_CSRRWI: begin
            imm_ext_op = CSR_TYPE;
            csr_op = CSR_WRITE;
            csr_bitmask_sel = CSR_BITMASK_SEL_IMM;
          end
          FUNCT3_CSRRSI: begin
            imm_ext_op = CSR_TYPE;
            csr_op = (rs1_addr_i == 0) ? CSR_READ : CSR_SET;
            csr_bitmask_sel = CSR_BITMASK_SEL_IMM;
          end
          FUNCT3_CSRRCI: begin
            imm_ext_op = CSR_TYPE;
            csr_op = (rs1_addr_i == 0) ? CSR_READ : CSR_CLEAR;
            csr_bitmask_sel = CSR_BITMASK_SEL_IMM;
          end
          default: begin
            illegal_instr_trap_o = 1;
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
        case (funct3_i)
          FUNCT3_SB: mem_op = MEM_SB;
          FUNCT3_SH: mem_op = MEM_SH;
          FUNCT3_SW: mem_op = MEM_SW;
          default: begin
            illegal_instr_trap_o = 1;
          end
        endcase
      end
      OPCODE_R_TYPE: begin
        if (is_unknown_rtype) begin
          illegal_instr_trap_o = 1;
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
          illegal_instr_trap_o = 1;
        end else begin
          rs1_valid = 1;
          rd_valid = 1;
          alu_a_src = ALU_A_SEL_REG_DATA;
          alu_b_src = ALU_B_SEL_IMM;
          alu_op = ALU_OP_IALU_ISHIFT_R_TYPE;
          pc_alu_src = PC_ALU_SEL_PC;
          case (funct3_i)
            3'b000, 3'b010, 3'b011, 3'b100, 3'b110, 3'b111: imm_ext_op = I_ALU_TYPE;  //I-type ALU
            3'b001, 3'b101: imm_ext_op = I_SHIFT_TYPE;  //I-type Shift
            default: begin
              illegal_instr_trap_o = 1;
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
        illegal_instr_trap_o = 1;
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
      case (funct3_i)
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

  assign rd_valid_o = rd_valid;
  assign rs1_valid_o = rs1_valid;
  assign rs2_valid_o = rs2_valid;
  assign mem_op_o = mem_op;
  assign cf_op_o = cf_op;
  assign csr_op_o = csr_op;
  assign alu_control_o = alu_control;
  assign imm_ext_op_o = imm_ext_op;
  assign alu_a_sel_o = alu_a_src;
  assign alu_b_sel_o = alu_b_src;
  assign pc_alu_sel_o = pc_alu_src;
  assign csr_bitmask_sel_o = csr_bitmask_sel;

endmodule
