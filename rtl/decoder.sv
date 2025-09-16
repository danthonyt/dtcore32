//===========================================================
// Project    : RISC-V CPU
// File       : decoder.sv
// Module     : decoder
// Description: Instruction decoder for RISC-V CPU. Decodes opcode, 
//              funct3/funct7/funct12 fields, and generates control 
//              signals for the ALU, immediate extension, CSR operations,
//              memory access, branching, and trap detection.
//
// Inputs:
//   op_i                - 7-bit opcode from instruction
//   funct3_i            - 3-bit funct3 field
//   funct7_i            - 7-bit funct7 field
//   funct12_i           - 12-bit funct12 field (for CSR/imm instructions)
//   rs1_addr_i          - Source register 1 address
//   rd_addr_i           - Destination register address
//   rtype_alt_i         - R-type instruction variant flag
//   itype_alt_i         - I-type instruction variant flag
//
// Outputs:
//   alu_control_o       - ALU operation type
//   imm_ext_op_o        - Immediate extension operation
//   alu_a_sel_o         - ALU input A selection
//   alu_b_sel_o         - ALU input B selection
//   pc_alu_sel_o        - PC/ALU selection signal
//   csr_bitmask_sel_o   - CSR bitmask selection
//   is_branch_o         - High if instruction is a branch
//   is_jump_o           - High if instruction is a jump
//   is_csr_write_o      - High if instruction writes to CSR
//   is_csr_read_o       - High if instruction reads from CSR
//   is_rd_write_o       - High if destination register is written
//   is_rs1_read_o       - High if source register 1 is read
//   is_rs2_read_o       - High if source register 2 is read
//   is_mem_write_o      - High if instruction writes to memory
//   is_mem_read_o       - High if instruction reads from memory
//   is_jal_o            - High if instruction is JAL
//   is_jalr_o           - High if instruction is JALR
//   is_memsize_b_o      - Memory byte size (signed)
//   is_memsize_bu_o     - Memory byte size (unsigned)
//   is_memsize_h_o      - Memory halfword size (signed)
//   is_memsize_hu_o     - Memory halfword size (unsigned)
//   is_memsize_w_o      - Memory word size
//   csr_op_rw_o         - CSR read/write operation
//   csr_op_clear_o      - CSR bit clear operation
//   csr_op_set_o        - CSR bit set operation
//   illegal_instr_trap_o- High if instruction is illegal
//   ecall_m_trap_o      - Machine environment call trap
//   breakpoint_trap_o   - Breakpoint trap
//
// Notes:
//   - Generates all control and side-effect signals required for 
//     instruction execution in the pipeline.
//   - Signals that may cause side effects (CSR/memory/branch) should 
//     be cleared on pipeline flushes.
//   - Designed to interface with ALU, CSR file, and memory units.
//
// Author     : David Torres
// Date       : 2025-09-16
//===========================================================

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

    // select signals
    output alu_control_t alu_control_o,
    output imm_ext_op_t imm_ext_op_o,
    output alu_a_sel_t alu_a_sel_o,
    output alu_b_sel_t alu_b_sel_o,
    output pc_alu_sel_t pc_alu_sel_o,
    output csr_bitmask_sel_t csr_bitmask_sel_o,

    // these signals cause side effects and 
    // must be cleared throughout the pipeline
    // on flushes
    output logic is_branch_o,
    output logic is_jump_o,
    output logic is_csr_write_o,
    output logic is_csr_read_o,
    output logic is_rd_write_o,
    output logic is_rs1_read_o,
    output logic is_rs2_read_o,
    output logic is_mem_write_o,
    output logic is_mem_read_o,
    
    // can leave unmodified during flushes
    output logic is_jal_o,
    output logic is_jalr_o,
    output logic is_memsize_b_o,
    output logic is_memsize_bu_o,
    output logic is_memsize_h_o,
    output logic is_memsize_hu_o,
    output logic is_memsize_w_o,
    output logic csr_op_rw_o,
    output logic csr_op_clear_o,
    output logic csr_op_set_o,
    output logic illegal_instr_trap_o,
    output logic ecall_m_trap_o,
    output logic breakpoint_trap_o

);

  logic illegal_instr_trap;
  logic ecall_m_trap;
  logic breakpoint_trap;

  logic is_branch;
  logic is_jump;
  logic is_jal;
  logic is_jalr;
  logic is_csr_write;
  logic is_csr_read;
  logic csr_op_rw;
  logic csr_op_clear;
  logic csr_op_set;
  logic is_rd_write;
  logic is_rs1_read;
  logic is_rs2_read;
  logic is_mem_write;
  logic is_mem_read;
  logic is_memsize_b;
  logic is_memsize_bu;
  logic is_memsize_h;
  logic is_memsize_hu;
  logic is_memsize_w;


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
    ecall_m_trap = 0;
    illegal_instr_trap = 0;
    breakpoint_trap = 0;
    // valid registers
    is_rd_write = 0;
    is_rs1_read = 0;
    is_rs2_read = 0;
    // mux select signals
    alu_op = ALU_OP_ILOAD_S_U_TYPE;
    alu_op = ALU_OP_ILOAD_S_U_TYPE;
    // control signals
    is_branch = 0;
    is_jump = 0;
    is_jal = 0;
    is_jalr = 0;
    is_csr_write = 0;
    is_csr_read = 0;
    csr_op_rw = 0;
    csr_op_clear = 0;
    csr_op_set = 0;
    is_rd_write = 0;
    is_rs1_read = 0;
    is_rs2_read = 0;
    is_mem_write = 0;
    is_mem_read = 0;
    is_memsize_b = 0;
    is_memsize_bu = 0;
    is_memsize_h = 0;
    is_memsize_hu = 0;
    is_memsize_w = 0;
    // sources
    imm_ext_op = I_ALU_TYPE;
    alu_a_src = ALU_A_SEL_REG_DATA;
    alu_b_src = ALU_B_SEL_REG_DATA;
    pc_alu_src = PC_ALU_SEL_PC;
    csr_bitmask_sel = CSR_BITMASK_SEL_REG_DATA;


    case (op_i)
      OPCODE_LOAD: begin
        imm_ext_op = I_ALU_TYPE;
        alu_a_src = ALU_A_SEL_REG_DATA;
        alu_b_src = ALU_B_SEL_IMM;
        alu_op = ALU_OP_ILOAD_S_U_TYPE;
        pc_alu_src = PC_ALU_SEL_PC;
        case (funct3_i)
          FUNCT3_LB: begin
            {is_rd_write, is_rs1_read, is_mem_read, is_memsize_b} = '1;
          end
          FUNCT3_LH: begin
            {is_rd_write, is_rs1_read, is_mem_read, is_memsize_h} = '1;
          end
          FUNCT3_LW: begin
            {is_rd_write, is_rs1_read, is_mem_read, is_memsize_w} = '1;
          end
          FUNCT3_LBU: begin
            {is_rd_write, is_rs1_read, is_mem_read, is_memsize_bu} = '1;
          end
          FUNCT3_LHU: begin
            {is_rd_write, is_rs1_read, is_mem_read, is_memsize_hu} = '1;
          end
          default: begin
            illegal_instr_trap = 1;
          end
        endcase
      end

      OPCODE_SYSCALL_CSR: begin
        case (funct3_i)
          FUNCT3_ECALL_EBREAK: begin
            if ((rs1_addr_i == 0) && (rd_addr_i == 0)) begin
              if (funct12_i == 12'h001) begin
                breakpoint_trap = 1;
              end else if (funct12_i == 12'h000) begin
                ecall_m_trap = 1;
              end else begin
                illegal_instr_trap = 1;
              end
            end else begin
              illegal_instr_trap = 1;
            end
          end
          // CSRRW/I always writes to the csr file, and conditionally reads when rd is not x0
          FUNCT3_CSRRW: begin
            {is_rs1_read, is_rd_write, is_csr_write, csr_op_rw} = '1;
            is_csr_read = (rd_addr_i != 0);
            csr_bitmask_sel = CSR_BITMASK_SEL_REG_DATA;
          end
          FUNCT3_CSRRWI: begin
            {is_rs1_read, is_rd_write, is_csr_write, csr_op_rw} = '1;
            is_csr_read = (rd_addr_i != 0);
            imm_ext_op = CSR_TYPE;
            csr_bitmask_sel = CSR_BITMASK_SEL_IMM;
          end
          // Others always read from the csr file, and conditionally writes when
          // rs1 is x0, or uimm is 0 for register and immediate operand types, respectively
          FUNCT3_CSRRS: begin
            {is_rs1_read, is_rd_write, is_csr_read, csr_op_set} = '1;
            is_csr_write = (rs1_addr_i != 0);
            csr_bitmask_sel = CSR_BITMASK_SEL_REG_DATA;
          end
          FUNCT3_CSRRSI: begin
            {is_rs1_read, is_rd_write, is_csr_read, csr_op_set} = '1;
            is_csr_write = (rs1_addr_i != 0);
            imm_ext_op = CSR_TYPE;
            csr_bitmask_sel = CSR_BITMASK_SEL_IMM;
          end
          FUNCT3_CSRRC: begin
            {is_rs1_read, is_rd_write, is_csr_read, csr_op_clear} = '1;
            is_csr_write = (rs1_addr_i != 0);
            csr_bitmask_sel = CSR_BITMASK_SEL_REG_DATA;
          end
          FUNCT3_CSRRCI: begin
            {is_rs1_read, is_rd_write, is_csr_read, csr_op_clear} = '1;
            is_csr_write = (rs1_addr_i != 0);
            imm_ext_op = CSR_TYPE;
            csr_bitmask_sel = CSR_BITMASK_SEL_IMM;
          end
          default: begin
            illegal_instr_trap = 1;
          end
        endcase
      end
      OPCODE_STORE: begin
        imm_ext_op = S_TYPE;
        alu_a_src = ALU_A_SEL_REG_DATA;
        alu_b_src = ALU_B_SEL_IMM;
        alu_op = ALU_OP_ILOAD_S_U_TYPE;
        pc_alu_src = PC_ALU_SEL_PC;
        case (funct3_i)
          FUNCT3_SB: begin
            {is_rs1_read, is_rs2_read, is_mem_write, is_memsize_b} = '1;
          end
          FUNCT3_SH: begin
            {is_rs1_read, is_rs2_read, is_mem_write, is_memsize_h} = '1;
          end
          FUNCT3_SW: begin
            {is_rs1_read, is_rs2_read, is_mem_write, is_memsize_w} = '1;
          end
          default: begin
            illegal_instr_trap = 1;
          end
        endcase
      end
      OPCODE_R_TYPE: begin
        if (is_unknown_rtype) begin
          illegal_instr_trap = 1;
        end else begin
          {is_rs1_read, is_rs2_read, is_rd_write} = '1;
          alu_a_src = ALU_A_SEL_REG_DATA;
          alu_b_src = ALU_B_SEL_REG_DATA;
          alu_op = ALU_OP_IALU_ISHIFT_R_TYPE;
          pc_alu_src = PC_ALU_SEL_PC;
        end
      end
      OPCODE_B_TYPE: begin
        {is_rs1_read, is_rs2_read, is_branch} = '1;
        imm_ext_op = B_TYPE;
        alu_a_src = ALU_A_SEL_REG_DATA;
        alu_b_src = ALU_B_SEL_REG_DATA;
        alu_op = ALU_OP_B_TYPE;
        pc_alu_src = PC_ALU_SEL_PC;
      end
      //I-type ALU or shift
      OPCODE_I_TYPE: begin
        if (is_unknown_itype) begin
          illegal_instr_trap = 1;
        end else begin
          alu_a_src = ALU_A_SEL_REG_DATA;
          alu_b_src = ALU_B_SEL_IMM;
          alu_op = ALU_OP_IALU_ISHIFT_R_TYPE;
          pc_alu_src = PC_ALU_SEL_PC;
          case (funct3_i)
            3'b000, 3'b010, 3'b011, 3'b100, 3'b110, 3'b111: begin
              {is_rs1_read, is_rd_write} = '1;
              imm_ext_op = I_ALU_TYPE;  //I-type ALU
            end
            3'b001, 3'b101: begin
              {is_rs1_read, is_rd_write} = '1;
              imm_ext_op = I_SHIFT_TYPE;  //I-type Shift
            end
            default: begin
              illegal_instr_trap = 1;
            end
          endcase  //I-type shift
        end
      end
      OPCODE_JAL: begin
        {is_rd_write, is_jump, is_jal} = '1;
        imm_ext_op = J_TYPE;
        alu_a_src = ALU_A_SEL_REG_DATA;
        alu_b_src = ALU_B_SEL_REG_DATA;
        alu_op = ALU_OP_ILOAD_S_U_TYPE;
        pc_alu_src = PC_ALU_SEL_PC;
      end
      OPCODE_U_TYPE_LUI: begin
        is_rd_write = 1;
        imm_ext_op = U_TYPE;
        alu_a_src = ALU_A_SEL_ZERO;
        alu_b_src = ALU_B_SEL_IMM;
        alu_op = ALU_OP_ILOAD_S_U_TYPE;
        pc_alu_src = PC_ALU_SEL_PC;
      end
      OPCODE_U_TYPE_AUIPC: begin
        is_rd_write = 1;
        imm_ext_op = U_TYPE;
        alu_a_src = ALU_A_SEL_PC;
        alu_b_src = ALU_B_SEL_IMM;
        alu_op = ALU_OP_ILOAD_S_U_TYPE;
        pc_alu_src = PC_ALU_SEL_PC;
      end
      OPCODE_JALR: begin
        {is_rs1_read, is_rd_write, is_jump, is_jalr} = '1;
        imm_ext_op = I_ALU_TYPE;
        alu_a_src = ALU_A_SEL_REG_DATA;
        alu_b_src = ALU_B_SEL_IMM;
        alu_op = ALU_OP_ILOAD_S_U_TYPE;
        pc_alu_src = PC_ALU_SEL_REG_DATA;
      end
      default: begin
        illegal_instr_trap = 1;
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
      //R-type, I-type ALU,I-type 1al shift
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
  assign imm_ext_op_o = imm_ext_op;
  assign alu_a_sel_o = alu_a_src;
  assign alu_b_sel_o = alu_b_src;
  assign pc_alu_sel_o = pc_alu_src;
  assign csr_bitmask_sel_o = csr_bitmask_sel;
  assign illegal_instr_trap_o = illegal_instr_trap;
  assign ecall_m_trap_o = ecall_m_trap;
  assign breakpoint_trap_o = breakpoint_trap;

  assign is_branch_o = is_branch;
  assign is_jump_o = is_jump;
  assign is_jal_o = is_jal;
  assign is_jalr_o = is_jalr;
  assign is_csr_write_o = is_csr_write;
  assign is_csr_read_o = is_csr_read;
  assign csr_op_rw_o = csr_op_rw;
  assign csr_op_clear_o = csr_op_clear;
  assign csr_op_set_o = csr_op_set;
  assign is_rd_write_o = (|rd_addr_i) ? is_rd_write : 0;
  assign is_rs1_read_o = is_rs1_read;
  assign is_rs2_read_o = is_rs2_read;
  assign is_mem_write_o = is_mem_write;
  assign is_mem_read_o = is_mem_read;
  assign is_memsize_b_o = is_memsize_b;
  assign is_memsize_bu_o = is_memsize_bu;
  assign is_memsize_h_o = is_memsize_h;
  assign is_memsize_hu_o = is_memsize_hu;
  assign is_memsize_w_o = is_memsize_w;


endmodule
