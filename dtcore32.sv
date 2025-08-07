
module dtcore32 (
    input  logic        clk_i,
    input  logic        rst_i,
    input  logic [31:0] IMEM_rdata_i,
    input  logic [31:0] DMEM_rdata_i,
`ifdef RISCV_FORMAL
    output logic        rvfi_valid,
    output logic [63:0] rvfi_order,
    output logic [31:0] rvfi_insn,
    output logic        rvfi_trap,
    output logic        rvfi_halt,
    output logic        rvfi_intr,
    output logic [ 1:0] rvfi_mode,
    output logic [ 1:0] rvfi_ixl,

    output logic [ 4:0] rvfi_rs1_addr,
    output logic [ 4:0] rvfi_rs2_addr,
    output logic [31:0] rvfi_rs1_rdata,
    output logic [31:0] rvfi_rs2_rdata,

    output logic [ 4:0] rvfi_rd_addr,
    output logic [31:0] rvfi_rd_wdata,

    output logic [31:0] rvfi_pc_rdata,
    output logic [31:0] rvfi_pc_wdata,

    output logic [31:0] rvfi_mem_addr,
    output logic [ 3:0] rvfi_mem_rmask,
    output logic [ 3:0] rvfi_mem_wmask,
    output logic [31:0] rvfi_mem_rdata,
    output logic [31:0] rvfi_mem_wdata,

    output logic [63:0] rvfi_csr_mcycle_rmask,
    output logic [63:0] rvfi_csr_mcycle_wmask,
    output logic [63:0] rvfi_csr_mcycle_rdata,
    output logic [63:0] rvfi_csr_mcycle_wdata,

    output logic [63:0] rvfi_csr_minstret_rmask,
    output logic [63:0] rvfi_csr_minstret_wmask,
    output logic [63:0] rvfi_csr_minstret_rdata,
    output logic [63:0] rvfi_csr_minstret_wdata,

    output logic [31:0] rvfi_csr_mcause_rmask,
    output logic [31:0] rvfi_csr_mcause_wmask,
    output logic [31:0] rvfi_csr_mcause_rdata,
    output logic [31:0] rvfi_csr_mcause_wdata,

    output logic [31:0] rvfi_csr_mepc_rmask,
    output logic [31:0] rvfi_csr_mepc_wmask,
    output logic [31:0] rvfi_csr_mepc_rdata,
    output logic [31:0] rvfi_csr_mepc_wdata,

    output logic [31:0] rvfi_csr_mtvec_rmask,
    output logic [31:0] rvfi_csr_mtvec_wmask,
    output logic [31:0] rvfi_csr_mtvec_rdata,
    output logic [31:0] rvfi_csr_mtvec_wdata,
`endif
    output logic [31:0] IMEM_addr_o,
    output logic [31:0] DMEM_addr_o,
    output logic [31:0] DMEM_wdata_o,
    output logic [ 3:0] DMEM_wmask_o
);
  /////////////////////////////////////////////
  //
  //  LOCAL PARAMETERS
  //
  //
  ////////////////////////////////////////////
  import params_pkg::*;

  ///////////////////////////////////////////////
  //
  //  SIGNAL DECLARATIONS
  //
  //
  ///////////////////////////////////////////////

  // IMEM AND DMEM SIGNALS
  logic [31:0] DMEM_addr_int;
  logic [3:0] DMEM_mem_wmask;
  // hazard unit signals
  // stops signals from propagating through the pipeline
  logic IF_stall;
  logic ID_stall;

  // resets the pipeline to control signals of a NOP instruction
  logic ID_flush;
  logic EX_flush;
  logic MEM1_flush;
  logic MEM2_flush;
  logic WB_flush;

  logic [31:0] IF_pc_tick;

  // instruction memory address of the instruction in the respective pipeline stage
  logic [31:0] IF_pc_rdata;
  logic [31:0] ID_pc_rdata;
  logic [31:0] EX_pc_rdata;
  logic [31:0] MEM1_pc_rdata;
  logic [31:0] MEM2_pc_rdata;
  logic [31:0] WB_pc_rdata;

  // the pc of the next instruction
  logic [31:0] EX_pc_wdata;
  logic [31:0] MEM1_pc_wdata;
  logic [31:0] MEM2_pc_wdata;
  logic [31:0] WB_pc_wdata;

  logic [31:0] exception_handler_addr;

  logic [31:0] IF_pc_plus_4;
  logic [31:0] ID_pc_plus_4;
  logic [31:0] EX_pc_plus_4;
  logic [31:0] MEM1_pc_plus_4;
  logic [31:0] MEM2_pc_plus_4;
  logic [31:0] WB_pc_plus_4;

  logic [31:0] ID_insn;
  logic [31:0] EX_insn;
  logic [31:0] MEM1_insn;
  logic [31:0] MEM2_insn;
  logic [31:0] WB_insn;

  logic ID_insn_en;
  logic EX_insn_en;
  logic WB_insn_en;



  trap_info_t IF_trap;
  trap_info_t ID_trap;
  trap_info_t EX_trap;
  trap_info_t MEM1_trap;
  trap_info_t MEM2_trap;
  trap_info_t WB_trap;

  trap_info_t ID_prev_trap;
  trap_info_t EX_prev_trap;
  trap_info_t MEM1_prev_trap;
  trap_info_t MEM2_prev_trap;
  trap_info_t WB_prev_trap;

  logic ID_reg_wr_en;
  logic EX_reg_wr_en;
  logic MEM1_reg_wr_en;
  logic MEM2_reg_wr_en;
  logic WB_reg_wr_en_int;
  logic WB_reg_wr_en;

  logic [2:0] ID_load_size;
  logic [2:0] EX_load_size;
  logic [2:0] MEM1_load_size;
  logic [2:0] MEM2_load_size;

  logic ID_jump;
  logic EX_jump;

  logic [31:0] ID_rs1_rdata;
  logic [31:0] ID_rs1_regfile_rdata;
  logic [31:0] EX_rs1_rdata_unforwarded;
  logic [31:0] EX_rs1_rdata;
  logic [31:0] MEM1_rs1_rdata;
  logic [31:0] MEM2_rs1_rdata;
  logic [31:0] WB_rs1_rdata;

  logic [31:0] ID_rs2_rdata;
  logic [31:0] ID_rs2_regfile_rdata;
  logic [31:0] EX_rs2_rdata_unforwarded;
  logic [31:0] EX_rs2_rdata;
  logic [31:0] MEM1_rs2_rdata;
  logic [31:0] MEM2_rs2_rdata;
  logic [31:0] WB_rs2_rdata;

  logic [4:0] ID_rs1_addr;
  logic [4:0] EX_rs1_addr;
  logic [4:0] MEM1_rs1_addr;
  logic [4:0] MEM2_rs1_addr;
  logic [4:0] WB_rs1_addr;

  logic [4:0] ID_rs2_addr;
  logic [4:0] EX_rs2_addr;
  logic [4:0] MEM1_rs2_addr;
  logic [4:0] MEM2_rs2_addr;
  logic [4:0] WB_rs2_addr;

  // actual csr being read/written
  logic [11:0] ID_csr_addr;
  logic [11:0] EX_csr_addr;
  logic [11:0] MEM1_csr_addr;
  logic [11:0] MEM2_csr_addr;
  logic [11:0] WB_csr_addr;

  // value used to write to a csr
  logic [31:0] EX_csr_wr_operand;
  logic [31:0] MEM1_csr_wr_operand;
  logic [31:0] MEM2_csr_wr_operand;
  logic [31:0] WB_csr_wr_operand;

  // 00 = no csr write, 01 = direct write, 10 = clear bitmask, 11 = set bitmask
  logic [1:0] ID_csr_wr_type;
  logic [1:0] EX_csr_wr_type;
  logic [1:0] MEM1_csr_wr_type;
  logic [1:0] MEM2_csr_wr_type;
  logic [1:0] WB_csr_wr_type_int;
  logic [1:0] WB_csr_wr_type;

  // 0 = register data value, 1 = immediate data value
  logic [1:0] ID_result_src;
  logic [1:0] EX_result_src;
  logic [1:0] MEM1_result_src;
  logic [1:0] MEM2_result_src;
  logic [1:0] WB_result_src;

  // 0 = register data value, 1 = immediate data value
  logic ID_csr_wr_operand_src;
  logic EX_csr_wr_operand_src;

  // extended immediate value depending on the immediate type
  logic [31:0] ID_imm_ext;
  logic [31:0] EX_imm_ext;

  // 00 = no write, 01 = word, 10 = half, 11 = byte
  logic [3:0] MEM1_mem_wmask;
  logic [3:0] MEM2_mem_wmask;
  logic [3:0] WB_mem_wmask;

  logic [3:0] MEM1_mem_rmask;
  logic [3:0] MEM2_mem_rmask;
  logic [3:0] WB_mem_rmask;

  logic [1:0] ID_mem_wr_size;
  logic [1:0] EX_mem_wr_size;
  logic [1:0] MEM1_mem_wr_size;

  // register destination for writes
  logic [4:0] ID_rd_addr;
  logic [4:0] EX_rd_addr;
  logic [4:0] MEM1_rd_addr;
  logic [4:0] MEM2_rd_addr;
  logic [4:0] WB_rd_addr, WB_rd_addr_int;

  // result of alu operation depending on the instruction type
  logic [31:0] EX_alu_result;
  logic [31:0] MEM1_alu_result;
  logic [31:0] MEM2_alu_result;
  logic [31:0] WB_alu_result;

  // 0 = pc, 1 = register source 1 data
  logic ID_pc_target_alu_src;
  logic EX_pc_target_alu_src;

  // read data from data memory
  logic [31:0] MEM2_mem_rdata;
  logic [31:0] WB_mem_rdata;

  // o = not a branch instruction, 1 = is a branch instruction
  logic ID_branch;
  logic EX_branch;

  logic [31:0] EX_mem_wdata_raw;
  logic [31:0] MEM1_mem_wdata_raw;

  logic [3:0] ID_alu_control;
  logic [3:0] EX_alu_control;

  logic ID_alu_b_src;
  logic EX_alu_b_src;

  logic [1:0] ID_alu_a_src;
  logic [1:0] EX_alu_a_src;

  logic [31:0] MEM1_mem_wdata;
  logic [31:0] MEM2_mem_wdata;
  logic [31:0] WB_mem_wdata;

  // 0 = not an actual instruction, or stalled.
  logic IF_valid_insn;
  logic ID_valid_insn;
  logic EX_valid_insn;
  logic MEM1_valid_insn;
  logic MEM2_valid_insn;
  logic WB_valid_insn;

  // used for rvfi interface
  logic IF_intr;
  logic ID_intr;
  logic EX_intr;
  logic MEM1_intr;
  logic MEM2_intr;
  logic WB_intr;

  // INSTRUCTION DECODE specific signals
  logic ID_is_ecall;
  logic ID_is_ebreak;
  logic [2:0] ID_imm_src;
  logic ID_opcode_exception;
  logic [6:0] ID_op;
  logic [2:0] ID_funct3;
  logic ID_funct7b5;
  logic [6:0] ID_funct7;
  logic [11:0] ID_funct12;
  logic ID_alu_op_exception;
  logic ID_funct7_exception;
  logic ID_unknown_insn;
  logic [1:0] ID_alu_op;
  logic ID_r_type_sub;
  logic ID_i_type_sub;
  logic ID_is_itype;
  logic ID_is_rtype;
  logic ID_is_SRA_or_SUB_funct3;
  logic ID_is_SLLI_or_SRLI_funct3;
  logic ID_is_SRAI_funct3;
  logic ID_unknown_itype;
  logic ID_unknown_rtype;
  logic ID_is_shift_itype;
  logic ID_forward_a;
  logic ID_forward_b;


  // EXECUTE stage specific signals
  logic [2:0] EX_forward_a;
  logic [2:0] EX_forward_b;
  logic EX_pc_src;
  logic [31:0] EX_pc_target;
  logic [31:0] EX_src_a_tick;
  logic [31:0] EX_src_a;
  logic [31:0] EX_src_b;
  logic [31:0] EX_pc_target_src_a;
  logic EX_branch_cond;
  logic EX_misaligned_jump_or_branch;
  logic [1:0] EX_result_src_lsb2_i;

  // DATA MEMORY stage specific signals
  logic MEM_misaligned_store;

  // WRITEBACK stage specific signals
  logic [31:0] WB_csr_rdata;  // reads the csr value before a write
  logic [31:0] WB_result;

  logic [31:0] WB_rd_wdata;

  logic ID_csr_rd_en;
  logic EX_csr_rd_en;
  logic MEM1_csr_rd_en;
  logic MEM2_csr_rd_en;
  logic WB_csr_rd_en;

  logic WB_csr_rd_en_int;

  logic [31:0] WB_csr_rmask;
  logic [31:0] WB_csr_wmask;

  logic [31:0] WB_csr_wdata;

  logic MEM2_load_trap_valid;
  logic [30:0] MEM2_load_trap_code;

  logic [30:0] MEM1_store_trap_code;
  logic MEM1_store_trap_valid;

  logic is_csr_mstatus;
  logic is_csr_misa;
  logic is_csr_mie;
  logic is_csr_mtvec;
  logic is_csr_mscratch;
  logic is_csr_mepc;
  logic is_csr_mcause;
  logic is_csr_mtval;
  logic is_csr_mip;
  logic is_csr_mcycle;
  logic is_csr_mcycleh;
  logic is_csr_minstret;
  logic is_csr_minstreth;
  logic is_csr_mvendorid;
  logic is_csr_marchid;
  logic is_csr_mimpid;
  logic is_csr_mhartid;
  logic is_csr_mconfigptr;

  //////////////////////////////////////
  //
  //  INSTRUCTION FETCH STAGE
  //
  //
  ///////////////////////////////////////


  // next pc logic
  always_comb begin
    unique case (EX_pc_src)
      // select pc incremented by 4
      1'b0: begin
        IF_pc_tick = IF_pc_plus_4;
      end
      // select pc from execute stage
      1'b1: begin
        IF_pc_tick = EX_pc_target;
      end
      default: begin
        IF_pc_tick = 0;
      end
    endcase
  end

  // pc incremented by 4
  assign IF_pc_plus_4 = IF_pc_rdata + 4;



  //////////////////////////////////////
  //
  //  INSTRUCTION DECODE STAGE
  //
  //
  ///////////////////////////////////////
  assign ID_op = ID_insn[6:0];
  assign ID_funct3 = ID_insn[14:12];
  assign ID_funct7b5 = ID_insn[30];
  assign ID_funct7 = ID_insn[31:25];
  assign ID_funct12 = ID_insn[31:20];
  logic ID_valid_rs1_addr;
  logic ID_valid_rs2_addr;
  logic ID_valid_rd_addr;

  assign ID_r_type_sub = ID_op[5] & ID_funct7b5;
  assign ID_i_type_sub = ~ID_op[5] & ID_funct7b5;
  assign ID_rs1_addr = (ID_valid_rs1_addr) ? ID_insn[19:15] : 0;
  assign ID_rs2_addr = (ID_valid_rs2_addr) ? ID_insn[24:20] : 0;
  assign ID_rd_addr = (ID_valid_rd_addr) ? ID_insn[11:7] : 0;
  assign ID_csr_addr = (ID_valid_insn) ? ID_insn[31:20] : 0; //ID_valid_insn//  INVALEID INSTRUCTION NOT HANDLED PROPERLY
  assign ID_unknown_insn = ID_opcode_exception | ID_alu_op_exception | ID_funct7_exception;

  assign ID_is_itype = (ID_op == OPCODE_I_TYPE) ? 1 : 0;
  assign ID_is_rtype = (ID_op == OPCODE_R_TYPE) ? 1 : 0;
  assign ID_is_SRAI_funct3 = (ID_funct3 == FUNCT3_SRAI) ? 1 : 0;
  assign ID_is_SRA_or_SUB_funct3 = ((ID_funct3 == FUNCT3_SRA) || (ID_funct3 == FUNCT3_SUB)) ? 1 : 0;
  assign ID_is_SLLI_or_SRLI_funct3 = ((ID_funct3 == FUNCT3_SLLI) || (ID_funct3 == FUNCT3_SRLI)) ? 1 : 0;
  assign ID_is_shift_itype = ID_is_SLLI_or_SRLI_funct3 | ID_is_SRAI_funct3;
  assign ID_unknown_rtype = ID_is_rtype 
                            & (ID_funct7 != 7'h00) 
                            & ~((ID_funct7 == 7'h20) & ID_is_SRA_or_SUB_funct3);
  assign ID_unknown_itype = ID_is_itype 
                            & ID_is_shift_itype
                            & ~(ID_is_SLLI_or_SRLI_funct3 & (ID_funct7 == 7'h00))
                            & ~(ID_is_SRAI_funct3 & (ID_funct7 == 7'h20));

  assign ID_funct7_exception = ID_unknown_rtype | ID_unknown_itype;
  // select forwarded rs1 or rs2 rdata if needed
  assign ID_rs1_rdata = ID_forward_a ? WB_rd_wdata : ID_rs1_regfile_rdata;
  assign ID_rs2_rdata = ID_forward_b ? WB_rd_wdata : ID_rs2_regfile_rdata;

  extend extend_inst (
      .insn_i(ID_insn),
      .imm_src_i(ID_imm_src),
      .imm_ext_o(ID_imm_ext)
  );

  // Decode the control signals for the specific instruction
  always_comb begin
    ID_valid_rd_addr = 0;
    ID_valid_rs1_addr = 0;
    ID_valid_rs2_addr = 0;
    ID_is_ebreak = 0;
    ID_is_ecall = 0;
    ID_opcode_exception = 0;
    ID_csr_rd_en = 0;
    // instructions should default to a nop
    ID_reg_wr_en = 0;
    ID_imm_src = I_ALU_TYPE_IMM_SRC;
    ID_alu_a_src = ALU_A_SRC_SELECT_REG_DATA;
    ID_alu_b_src = ALU_B_SRC_SELECT_REG_DATA;
    ID_mem_wr_size = MEM_NO_DMEM_WR;
    ID_result_src = RESULT_SRC_SELECT_ALU_RESULT;
    ID_branch = IS_NOT_BRANCH_INSTR;
    ID_alu_op = ALU_OP_ILOAD_S_U_TYPE;
    ID_jump = IS_NOT_JUMP_INSTR;
    ID_pc_target_alu_src = PC_TARGET_ALU_SRC_SELECT_PC;
    ID_load_size = DMEM_LOAD_SIZE_NO_LOAD;
    ID_csr_wr_type = CSR_WRITE_DISABLE;
    ID_csr_wr_operand_src = CSR_SRC_SELECT_REG_DATA;
    case (ID_op)
      OPCODE_LOAD: begin
        ID_valid_rs1_addr = 1;
        ID_valid_rd_addr = 1;

        ID_reg_wr_en = REGFILE_WRITE_ENABLE;
        ID_imm_src = I_ALU_TYPE_IMM_SRC;
        ID_alu_a_src = ALU_A_SRC_SELECT_REG_DATA;
        ID_alu_b_src = ALU_B_SRC_SELECT_IMM;
        ID_result_src = RESULT_SRC_SELECT_DMEM_RD_DATA;
        ID_alu_op = ALU_OP_ILOAD_S_U_TYPE;
        ID_pc_target_alu_src = PC_TARGET_ALU_SRC_SELECT_PC;
        case (ID_funct3)
          FUNCT3_LB:  ID_load_size = DMEM_LOAD_SIZE_BYTE;
          FUNCT3_LH:  ID_load_size = DMEM_LOAD_SIZE_HALF;
          FUNCT3_LW:  ID_load_size = DMEM_LOAD_SIZE_WORD;
          FUNCT3_LBU: ID_load_size = DMEM_LOAD_SIZE_BYTEU;
          FUNCT3_LHU: ID_load_size = DMEM_LOAD_SIZE_HALFU;
          default: begin
            ID_opcode_exception = 1;
          end
        endcase
      end

      OPCODE_SYSCALL_CSR: begin
        ID_valid_rs1_addr = 1;
        ID_valid_rd_addr  = 1;
        case (ID_funct3)
          FUNCT3_ECALL_EBREAK: begin
            if ((ID_rs1_addr == 0) && (ID_rd_addr == 0)) begin
              if (ID_funct12 == 12'h001) ID_is_ebreak = 1;
              else if (ID_funct12 == 12'h000) ID_is_ecall = 1;
              else ID_opcode_exception = 1;
            end
            else ID_opcode_exception = 1;
          end
          FUNCT3_CSRRW: begin
            ID_reg_wr_en = REGFILE_WRITE_ENABLE;
            ID_result_src = RESULT_SRC_SELECT_CSR_READ_DATA;
            ID_csr_wr_type = CSR_WRITE_RAW_VALUE;
            ID_csr_wr_operand_src = CSR_SRC_SELECT_REG_DATA;
            ID_csr_rd_en = 1;
          end
          FUNCT3_CSRRS: begin
            ID_reg_wr_en = REGFILE_WRITE_ENABLE;
            ID_result_src = RESULT_SRC_SELECT_CSR_READ_DATA;
            ID_csr_wr_type = (ID_rs1_addr == 0) ? CSR_WRITE_DISABLE : CSR_WRITE_SET_BIT_MASK;
            ID_csr_wr_operand_src = CSR_SRC_SELECT_REG_DATA;
            ID_csr_rd_en = 1;
          end
          FUNCT3_CSRRC: begin
            ID_reg_wr_en = REGFILE_WRITE_ENABLE;
            ID_result_src = RESULT_SRC_SELECT_CSR_READ_DATA;
            ID_csr_wr_type = (ID_rs1_addr == 0) ? CSR_WRITE_DISABLE : CSR_WRITE_CLEAR_BIT_MASK;
            ID_csr_wr_operand_src = CSR_SRC_SELECT_REG_DATA;
            ID_csr_rd_en = 1;
          end
          FUNCT3_CSRRWI: begin
            ID_reg_wr_en = REGFILE_WRITE_ENABLE;
            ID_result_src = RESULT_SRC_SELECT_CSR_READ_DATA;
            ID_imm_src = CSR_TYPE_IMM_SRC;
            ID_csr_wr_type = CSR_WRITE_RAW_VALUE;
            ID_csr_wr_operand_src = CSR_SRC_SELECT_IMM;
            ID_csr_rd_en = 1;
          end
          FUNCT3_CSRRSI: begin
            ID_reg_wr_en = REGFILE_WRITE_ENABLE;
            ID_result_src = RESULT_SRC_SELECT_CSR_READ_DATA;
            ID_imm_src = CSR_TYPE_IMM_SRC;
            ID_csr_wr_type = (ID_rs1_addr == 0) ? CSR_WRITE_DISABLE : CSR_WRITE_SET_BIT_MASK;
            ID_csr_wr_operand_src = CSR_SRC_SELECT_IMM;
            ID_csr_rd_en = 1;
          end
          FUNCT3_CSRRCI: begin
            ID_reg_wr_en = REGFILE_WRITE_ENABLE;
            ID_result_src = RESULT_SRC_SELECT_CSR_READ_DATA;
            ID_imm_src = CSR_TYPE_IMM_SRC;
            ID_csr_wr_type = (ID_rs1_addr == 0) ? CSR_WRITE_DISABLE : CSR_WRITE_CLEAR_BIT_MASK;
            ID_csr_wr_operand_src = CSR_SRC_SELECT_IMM;
            ID_csr_rd_en = 1;
          end
          default: begin
            ID_opcode_exception = 1;
          end
        endcase
      end
      OPCODE_STORE: begin
        ID_valid_rs1_addr = 1;
        ID_valid_rs2_addr = 1;
        ID_imm_src = S_TYPE_IMM_SRC;
        ID_alu_a_src = ALU_A_SRC_SELECT_REG_DATA;
        ID_alu_b_src = ALU_B_SRC_SELECT_IMM;
        ID_alu_op = ALU_OP_ILOAD_S_U_TYPE;
        ID_pc_target_alu_src = PC_TARGET_ALU_SRC_SELECT_PC;
        case (ID_funct3)
          FUNCT3_SB: ID_mem_wr_size = MEM_BYTE_WR;  //sb
          FUNCT3_SH: ID_mem_wr_size = MEM_HALF_WR;  //sh
          FUNCT3_SW: ID_mem_wr_size = MEM_WORD_WR;  //sw
          default: begin
            ID_opcode_exception = 1;
          end
        endcase
      end
      OPCODE_R_TYPE: begin
        ID_valid_rs1_addr = 1;
        ID_valid_rs2_addr = 1;
        ID_valid_rd_addr = 1;
        ID_reg_wr_en = REGFILE_WRITE_ENABLE;
        ID_alu_a_src = ALU_A_SRC_SELECT_REG_DATA;
        ID_alu_b_src = ALU_B_SRC_SELECT_REG_DATA;
        ID_result_src = RESULT_SRC_SELECT_ALU_RESULT;
        ID_alu_op = ALU_OP_IALU_ISHIFT_R_TYPE;
        ID_pc_target_alu_src = PC_TARGET_ALU_SRC_SELECT_PC;
      end
      OPCODE_B_TYPE: begin
        ID_valid_rs1_addr = 1;
        ID_valid_rs2_addr = 1;
        ID_reg_wr_en = 0;
        ID_imm_src = B_TYPE_IMM_SRC;
        ID_alu_a_src = ALU_A_SRC_SELECT_REG_DATA;
        ID_alu_b_src = ALU_B_SRC_SELECT_REG_DATA;
        ID_branch = IS_BRANCH_INSTR;
        ID_alu_op = ALU_OP_B_TYPE;
        ID_pc_target_alu_src = PC_TARGET_ALU_SRC_SELECT_PC;
      end
      //I-type ALU or shift
      OPCODE_I_TYPE: begin
        ID_valid_rs1_addr = 1;
        ID_valid_rd_addr = 1;
        ID_reg_wr_en = REGFILE_WRITE_ENABLE;
        ID_alu_a_src = ALU_A_SRC_SELECT_REG_DATA;
        ID_alu_b_src = ALU_B_SRC_SELECT_IMM;
        ID_result_src = RESULT_SRC_SELECT_ALU_RESULT;
        ID_alu_op = ALU_OP_IALU_ISHIFT_R_TYPE;
        ID_pc_target_alu_src = PC_TARGET_ALU_SRC_SELECT_PC;
        case (ID_funct3)
          3'b000, 3'b010, 3'b011, 3'b100, 3'b110, 3'b111:
          ID_imm_src = I_ALU_TYPE_IMM_SRC;  //I-type ALU
          3'b001, 3'b101: ID_imm_src = I_SHIFT_TYPE_IMM_SRC;  //I-type Shift
          default: begin
            ID_imm_src = I_ALU_TYPE_IMM_SRC;  //unknown instruction
            ID_opcode_exception = 1;
          end
        endcase  //I-type shift
      end
      OPCODE_JAL: begin
        ID_valid_rd_addr = 1;
        ID_reg_wr_en = REGFILE_WRITE_ENABLE;
        ID_imm_src = J_TYPE_IMM_SRC;
        ID_alu_a_src = ALU_A_SRC_SELECT_REG_DATA;
        ID_alu_b_src = ALU_B_SRC_SELECT_REG_DATA;
        ID_result_src = RESULT_SRC_SELECT_NEXT_INSTR_ADDR;
        ID_alu_op = ALU_OP_ILOAD_S_U_TYPE;
        ID_jump = IS_JUMP_INSTR;
        ID_pc_target_alu_src = PC_TARGET_ALU_SRC_SELECT_PC;
      end
      OPCODE_U_TYPE_LUI: begin
        ID_valid_rd_addr = 1;
        ID_reg_wr_en = REGFILE_WRITE_ENABLE;
        ID_imm_src = U_TYPE_IMM_SRC;
        ID_alu_a_src = ALU_A_SRC_SELECT_ZERO;
        ID_alu_b_src = ALU_B_SRC_SELECT_IMM;
        ID_result_src = RESULT_SRC_SELECT_ALU_RESULT;
        ID_alu_op = ALU_OP_ILOAD_S_U_TYPE;
        ID_pc_target_alu_src = PC_TARGET_ALU_SRC_SELECT_PC;
      end
      OPCODE_U_TYPE_AUIPC: begin
        ID_valid_rd_addr = 1;
        ID_reg_wr_en = REGFILE_WRITE_ENABLE;
        ID_imm_src = U_TYPE_IMM_SRC;
        ID_alu_a_src = ALU_A_SRC_SELECT_PC;
        ID_alu_b_src = ALU_B_SRC_SELECT_IMM;
        ID_result_src = RESULT_SRC_SELECT_ALU_RESULT;
        ID_alu_op = ALU_OP_ILOAD_S_U_TYPE;
        ID_pc_target_alu_src = PC_TARGET_ALU_SRC_SELECT_PC;
      end
      OPCODE_JALR: begin
        ID_valid_rs1_addr = 1;
        ID_valid_rd_addr = 1;
        ID_reg_wr_en = REGFILE_WRITE_ENABLE;
        ID_imm_src = I_ALU_TYPE_IMM_SRC;
        ID_alu_a_src = ALU_A_SRC_SELECT_REG_DATA;
        ID_alu_b_src = ALU_B_SRC_SELECT_IMM;
        ID_result_src = RESULT_SRC_SELECT_NEXT_INSTR_ADDR;
        ID_alu_op = ALU_OP_ILOAD_S_U_TYPE;
        ID_jump = IS_JUMP_INSTR;
        ID_pc_target_alu_src = PC_TARGET_ALU_SRC_SELECT_REG_DATA;
      end
      default: begin
        ID_opcode_exception = 1;
      end
    endcase
  end
  // decode the alu operation used for the instruction
  always_comb begin
    ID_alu_op_exception = 0;
    ID_alu_control = 0;
    case (ID_alu_op)
      //I-type Load, S-type, U-type
      ALU_OP_ILOAD_S_U_TYPE:
      ID_alu_control = ADD_ALU_CONTROL;  //add- lw,sw,lb,lh,lbu,lhu,sb,sh,auipc,lui
      //B-type
      ALU_OP_B_TYPE:
      case (ID_funct3)
        FUNCT3_BEQ:  ID_alu_control = SUB_ALU_CONTROL;  //sub - beq
        FUNCT3_BNE:  ID_alu_control = BNE_ALU_CONTROL;  //sub - bne
        FUNCT3_BLT:  ID_alu_control = LT_ALU_CONTROL;  //blt
        FUNCT3_BGE:  ID_alu_control = GE_ALU_CONTROL;  //bge
        FUNCT3_BLTU: ID_alu_control = LTU_ALU_CONTROL;  //bltu
        FUNCT3_BGEU: ID_alu_control = GEU_ALU_CONTROL;  //bgeu
        default: begin
          ID_alu_op_exception = 1;
        end
      endcase
      //R-type, I-type ALU,I-type logical shift
      ALU_OP_IALU_ISHIFT_R_TYPE: begin
        case (ID_funct3)
          FUNCT3_ADD:
          ID_alu_control = (ID_r_type_sub) ? SUB_ALU_CONTROL  /*sub*/ : ADD_ALU_CONTROL  /*add*/;
          FUNCT3_SLL: ID_alu_control = L_SHIFT_ALU_CONTROL;  //sll
          FUNCT3_SLT: ID_alu_control = LT_ALU_CONTROL;  //slt
          FUNCT3_SLTU_SLTIU: ID_alu_control = LTU_ALU_CONTROL;  //sltu, sltiu
          FUNCT3_XOR: ID_alu_control = XOR_ALU_CONTROL;  //xor
          FUNCT3_SRA:
          ID_alu_control = (ID_r_type_sub || ID_i_type_sub) ? R_SHIFT_A_ALU_CONTROL /*sra*/ : R_SHIFT_L_ALU_CONTROL /*srl*/;
          FUNCT3_OR: ID_alu_control = OR_ALU_CONTROL;  //or
          FUNCT3_AND: ID_alu_control = AND_ALU_CONTROL;  //and
          default: ID_alu_op_exception = 1;
        endcase
      end
      default: ;
    endcase
  end
  // register file
  dtcore32_regfile dtcore32_regfile_inst (
      .clk_i(clk_i),
      .rst_i(rst_i),
      .rs1_addr_i(ID_rs1_addr),
      .rs2_addr_i(ID_rs2_addr),
      .rd_addr_i(WB_rd_addr),
      .reg_wr_data_i(WB_rd_wdata),
      .rs1_rdata_o(ID_rs1_regfile_rdata),
      .rs2_rdata_o(ID_rs2_regfile_rdata)
  );



  //////////////////////////////////////
  //
  //
  //
  //
  // INSTRUCTION EXECUTE STAGE
  //
  //
  //
  //
  ///////////////////////////////////////
  assign EX_rs1_rdata = EX_src_a_tick;
  assign EX_rs2_rdata = EX_mem_wdata_raw;
  assign EX_insn_en = ~EX_prev_trap.valid;
  assign EX_pc_src = (EX_jump | (EX_branch & EX_branch_cond)) & EX_insn_en;

  assign EX_pc_wdata = EX_pc_src ? EX_pc_target : EX_pc_plus_4;
  // trap if a jump or branch address is misaligned
  assign EX_misaligned_jump_or_branch = EX_pc_src & (IF_pc_tick[1] | IF_pc_tick[0]);
  // alu input 1 data path
  // select reg 1 data or data forwarded from WB or MEM stage
  always_comb begin
    case (EX_forward_a)
      FORWARD_SEL_NO_FORWARD:        EX_src_a_tick = EX_rs1_rdata_unforwarded;
      FORWARD_SEL_MEM1_ALU_RESULT:   EX_src_a_tick = MEM1_alu_result;
      FORWARD_SEL_MEM2_ALU_RESULT:   EX_src_a_tick = MEM2_alu_result;
      FORWARD_SEL_MEM2_MEM_RDATA:    EX_src_a_tick = MEM2_mem_rdata;
      FORWARD_SEL_WB_RESULT:         EX_src_a_tick = WB_result;
      default:                       EX_src_a_tick = 0;
    endcase
  end
  // select data from first mux, zero, or pc
  always_comb begin
    case (EX_alu_a_src)
      2'b00:   EX_src_a = EX_src_a_tick;
      2'b01:   EX_src_a = 0;
      2'b10:   EX_src_a = EX_pc_rdata;
      default: EX_src_a = 0;
    endcase
  end
  // alu input 2 data path
  // select reg 2 data or data forwarded from WB or MEM stage
  always_comb begin
    case (EX_forward_b)
      FORWARD_SEL_NO_FORWARD:        EX_mem_wdata_raw = EX_rs2_rdata_unforwarded;
      FORWARD_SEL_MEM1_ALU_RESULT:   EX_mem_wdata_raw = MEM1_alu_result;
      FORWARD_SEL_MEM2_ALU_RESULT:   EX_mem_wdata_raw = MEM2_alu_result;
      FORWARD_SEL_MEM2_MEM_RDATA:    EX_mem_wdata_raw = MEM2_mem_rdata;
      FORWARD_SEL_WB_RESULT:         EX_mem_wdata_raw = WB_result;
      default:                       EX_mem_wdata_raw = 0;
    endcase
  end
  // select data from first mux, or extended immediate
  always_comb begin
    unique case (EX_alu_b_src)
      1'b0: EX_src_b = EX_mem_wdata_raw;
      1'b1: EX_src_b = EX_imm_ext;
    endcase
  end
  // select base address for branch/jump address, selecting either
  // the current pc or reg1_data.
  always_comb begin
    unique case (EX_pc_target_alu_src)
      1'b0: EX_pc_target_src_a = EX_pc_rdata;
      1'b1: EX_pc_target_src_a = EX_src_a_tick;
    endcase
  end
  // select write value to be used in a csr instruction
  always_comb begin
    unique case (EX_csr_wr_operand_src)
      1'b0: EX_csr_wr_operand = EX_src_a_tick;
      1'b1: EX_csr_wr_operand = EX_imm_ext;
    endcase
  end
  assign EX_pc_target = EX_pc_target_src_a + EX_imm_ext;

  alu alu_inst (
      .a_i(EX_src_a),
      .b_i(EX_src_b),
      .control_i(EX_alu_control),
      .branch_cond_o(EX_branch_cond),
      .result_o(EX_alu_result)
  );

  csr_regfile csr_regfile_inst (
      .clk_i(clk_i),
      .rst_i(rst_i),
      .WB_rd_addr_i(WB_rd_addr),
      .csr_addr_i(WB_csr_addr),
      .WB_valid_insn_i(WB_valid_insn),
      .WB_trap_i(WB_trap),
      .csr_wtype_i(WB_csr_wr_type),
      .csr_woperand(WB_csr_wr_operand),
      .trap_handler_addr_o(exception_handler_addr),
      .csr_rdata_o(WB_csr_rdata),
      .csr_rmask_o(WB_csr_rmask),
      .csr_wdata_o(WB_csr_wdata),
      .csr_wmask_o(WB_csr_wmask)
  );


  //////////////////////////////////////
  //
  //  DATA MEMORY 1 STAGE
  //
  //
  ///////////////////////////////////////

  store_unit store_unit_inst (
      .store_size_i(MEM1_mem_wr_size),
      .addr_lsb2_i(MEM1_alu_result[1:0]),
      .wdata_unformatted_i(MEM1_mem_wdata_raw),
      .store_trap_o(MEM1_store_trap_valid),
      .trap_code_o(MEM1_store_trap_code),
      .wmask_o(MEM1_mem_wmask),
      .wdata_formatted_o(MEM1_mem_wdata)
  );



  //////////////////////////////////////
  //
  //  DATA MEMORY 2 STAGE
  //
  //
  ///////////////////////////////////////
  load_unit load_unit_inst (
      .load_type(MEM2_load_size),
      .addr_lsb2(MEM2_alu_result[1:0]),
      .rdata_unformatted_i(DMEM_rdata_i),
      .load_trap_o(MEM2_load_trap_valid),
      .load_trap_code_o(MEM2_load_trap_code),
      .rmask_o(MEM2_mem_rmask),
      .rdata_formatted_o(MEM2_mem_rdata)
  );

  //////////////////////////////////////
  //
  //  WRITEBACK STAGE
  //
  //
  ///////////////////////////////////////

  // disable register and csr writes for an excepted instruction
  assign WB_insn_en = ~WB_trap.valid;
  assign WB_reg_wr_en = WB_insn_en ? WB_reg_wr_en_int : 0;
  assign WB_csr_wr_type = WB_insn_en ? WB_csr_wr_type_int : 0;
  assign WB_csr_rd_en = WB_insn_en ? WB_csr_rd_en_int : 0;
  // make sure that instructions that dont write to any register address have x0 as rd and 0 as rd_wdata
  assign WB_rd_wdata = ((WB_rd_addr != 0) & WB_reg_wr_en) ? WB_result : 0;
  assign WB_rd_addr = (WB_reg_wr_en) ? WB_rd_addr_int : 0;
  always_comb begin
    unique case (WB_result_src)
      2'b00: WB_result = WB_alu_result;
      2'b01: WB_result = WB_mem_rdata;
      2'b10: WB_result = WB_pc_plus_4;
      2'b11: WB_result = WB_csr_rdata;
    endcase
  end

  //////////////////////////////////////
  //
  //  PIPELINE REGISTERS
  //
  //
  ///////////////////////////////////////
  // IF
  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      IF_pc_rdata <= 0;
      IF_intr <= 0;
      IF_valid_insn <= 1;
    end else if (WB_trap.valid) begin  // jump to trap handler if retired instrucion has a trap
      IF_pc_rdata <= exception_handler_addr;
      IF_intr <= 1;
      IF_valid_insn <= 1;
    end else if (!IF_stall) begin
      IF_pc_rdata <= IF_pc_tick;
      IF_intr <= 0;
      IF_valid_insn <= 1;
    end
  end
  //IF/ID
  always_ff @(posedge clk_i) begin
    if (rst_i || ID_flush) begin
      ID_insn <= NOP_INSTRUCTION;
      ID_pc_rdata <= 0;
      ID_pc_plus_4 <= 0;
      ID_prev_trap <= '{default: 0};
      ID_valid_insn <= 0;
      ID_intr <= 0;
    end else if (IF_trap.valid) begin
      ID_insn <= NOP_INSTRUCTION;
      ID_pc_rdata <= 0;
      ID_pc_plus_4 <= 0;
      ID_prev_trap <= IF_trap;
      ID_valid_insn <= 1;
      ID_intr <= 0;
    end else if (!ID_stall) begin
      ID_insn <= IMEM_rdata_i;
      ID_pc_rdata <= IF_pc_rdata;
      ID_pc_plus_4 <= IF_pc_plus_4;
      ID_prev_trap <= IF_trap;
      ID_valid_insn <= IF_valid_insn;
      ID_intr <= IF_intr;
    end
  end
  // ID/EX register
  always_ff @(posedge clk_i) begin
    if (rst_i || EX_flush || ID_stall) begin
      EX_reg_wr_en <= 0;
      EX_result_src <= 0;
      EX_load_size <= 0;
      EX_mem_wr_size <= 0;
      EX_jump <= 0;
      EX_branch <= 0;
      EX_alu_control <= 0;
      EX_alu_a_src <= 0;
      EX_alu_b_src <= 1;
      EX_pc_target_alu_src <= 0;
      EX_rs1_rdata_unforwarded <= 0;
      EX_rs2_rdata_unforwarded <= 0;
      EX_pc_rdata <= 0;
      EX_rs1_addr <= 0;
      EX_rs2_addr <= 0;
      EX_rd_addr <= 0;
      EX_imm_ext <= 0;
      EX_pc_plus_4 <= 0;
      EX_insn <= NOP_INSTRUCTION;
      EX_prev_trap <= '{default: 0};
      EX_csr_addr <= 0;
      EX_csr_wr_operand_src <= 0;
      EX_csr_wr_type <= 0;
      EX_valid_insn <= 0;
      EX_intr <= 0;
      EX_csr_rd_en <= 0;
    end else if (ID_trap.valid) begin
      EX_reg_wr_en <= 0;
      EX_result_src <= 0;
      EX_load_size <= 0;
      EX_mem_wr_size <= 0;
      EX_jump <= 0;
      EX_branch <= 0;
      EX_alu_control <= 0;
      EX_alu_a_src <= 0;
      EX_alu_b_src <= 1;
      EX_pc_target_alu_src <= 0;
      EX_rs1_rdata_unforwarded <= 0;
      EX_rs2_rdata_unforwarded <= 0;
      EX_pc_rdata <= 0;
      EX_rs1_addr <= 0;
      EX_rs2_addr <= 0;
      EX_rd_addr <= 0;
      EX_imm_ext <= 0;
      EX_pc_plus_4 <= 0;
      EX_insn <= NOP_INSTRUCTION;
      EX_prev_trap <= ID_trap;
      EX_csr_addr <= 0;
      EX_csr_wr_operand_src <= 0;
      EX_csr_wr_type <= 0;
      EX_valid_insn <= 1;
      EX_intr <= 0;
      EX_csr_rd_en <= 0;
    end else begin
      EX_reg_wr_en <= ID_reg_wr_en;
      EX_result_src <= ID_result_src;
      EX_load_size <= ID_load_size;
      EX_mem_wr_size <= ID_mem_wr_size;
      EX_jump <= ID_jump;
      EX_branch <= ID_branch;
      EX_alu_control <= ID_alu_control;
      EX_alu_a_src <= ID_alu_a_src;
      EX_alu_b_src <= ID_alu_b_src;
      EX_pc_target_alu_src <= ID_pc_target_alu_src;
      EX_rs1_rdata_unforwarded <= ID_rs1_rdata;
      EX_rs2_rdata_unforwarded <= ID_rs2_rdata;
      EX_pc_rdata <= ID_pc_rdata;
      EX_rs1_addr <= ID_rs1_addr;
      EX_rs2_addr <= ID_rs2_addr;
      EX_rd_addr <= ID_rd_addr;
      EX_imm_ext <= ID_imm_ext;
      EX_pc_plus_4 <= ID_pc_plus_4;
      EX_insn <= ID_insn;
      EX_prev_trap <= ID_trap;
      EX_csr_addr <= ID_csr_addr;
      EX_csr_wr_operand_src <= ID_csr_wr_operand_src;
      EX_csr_wr_type <= ID_csr_wr_type;
      EX_valid_insn <= ID_valid_insn;
      EX_intr <= ID_intr;
      EX_csr_rd_en <= ID_csr_rd_en;
    end
  end
  // EX/MEM1 register
  always_ff @(posedge clk_i) begin
    if (rst_i || MEM1_flush) begin
      MEM1_reg_wr_en <= 0;
      MEM1_result_src <= 0;
      MEM1_load_size <= 0;
      MEM1_mem_wr_size <= 0;
      MEM1_alu_result <= 0;
      MEM1_mem_wdata_raw <= 0;
      MEM1_rd_addr <= 0;
      MEM1_pc_rdata <= 0;
      MEM1_pc_plus_4 <= 0;
      MEM1_prev_trap <= '{default: 0};
      MEM1_insn <= NOP_INSTRUCTION;
      MEM1_csr_addr <= 0;
      MEM1_csr_wr_operand <= 0;
      MEM1_csr_wr_type <= 0;
      MEM1_valid_insn <= 0;
      MEM1_intr <= 0;
      MEM1_rs1_rdata <= 0;
      MEM1_rs2_rdata <= 0;
      MEM1_rs1_addr <= 0;
      MEM1_rs2_addr <= 0;
      MEM1_csr_rd_en <= 0;
      MEM1_pc_wdata <= 0;
    end else if (EX_trap.valid) begin
      MEM1_reg_wr_en <= 0;
      MEM1_result_src <= 0;
      MEM1_load_size <= 0;
      MEM1_mem_wr_size <= 0;
      MEM1_alu_result <= 0;
      MEM1_mem_wdata_raw <= 0;
      MEM1_rd_addr <= 0;
      MEM1_pc_rdata <= 0;
      MEM1_pc_plus_4 <= 0;
      MEM1_prev_trap <= EX_trap;
      MEM1_insn <= NOP_INSTRUCTION;
      MEM1_csr_addr <= 0;
      MEM1_csr_wr_operand <= 0;
      MEM1_csr_wr_type <= 0;
      MEM1_valid_insn <= 1;
      MEM1_intr <= 0;
      MEM1_rs1_rdata <= 0;
      MEM1_rs2_rdata <= 0;
      MEM1_rs1_addr <= 0;
      MEM1_rs2_addr <= 0;
      MEM1_csr_rd_en <= 0;
      MEM1_pc_wdata <= 0;
    end else begin
      MEM1_reg_wr_en <= EX_reg_wr_en;
      MEM1_result_src <= EX_result_src;
      MEM1_load_size <= EX_load_size;
      MEM1_mem_wr_size <= EX_mem_wr_size;
      MEM1_alu_result <= EX_alu_result;
      MEM1_mem_wdata_raw <= EX_mem_wdata_raw;
      MEM1_rd_addr <= EX_rd_addr;
      MEM1_pc_rdata <= EX_pc_rdata;
      MEM1_pc_plus_4 <= EX_pc_plus_4;
      MEM1_prev_trap <= EX_trap;
      MEM1_insn <= EX_insn;
      MEM1_csr_addr <= EX_csr_addr;
      MEM1_csr_wr_operand <= EX_csr_wr_operand;
      MEM1_csr_wr_type <= EX_csr_wr_type;
      MEM1_valid_insn <= EX_valid_insn;
      MEM1_intr <= EX_intr;
      MEM1_rs1_rdata <= EX_rs1_rdata;
      MEM1_rs2_rdata <= EX_rs2_rdata;
      MEM1_rs1_addr <= EX_rs1_addr;
      MEM1_rs2_addr <= EX_rs2_addr;
      MEM1_csr_rd_en <= EX_csr_rd_en;
      MEM1_pc_wdata <= EX_pc_wdata;
    end
  end
  // MEM1/MEM2
  always_ff @(posedge clk_i) begin
    if (rst_i || MEM2_flush) begin
      MEM2_reg_wr_en <= 0;
      MEM2_result_src <= 0;
      MEM2_load_size <= 0;
      MEM2_alu_result <= 0;
      MEM2_rd_addr <= 0;
      MEM2_pc_rdata <= 0;
      MEM2_pc_plus_4 <= 0;
      MEM2_prev_trap <= '{default: 0};
      MEM2_insn <= NOP_INSTRUCTION;
      MEM2_csr_addr <= 0;
      MEM2_csr_wr_operand <= 0;
      MEM2_csr_wr_type <= 0;
      MEM2_valid_insn <= 0;
      MEM2_intr <= 0;
      MEM2_rs1_rdata <= 0;
      MEM2_rs2_rdata <= 0;
      MEM2_rs1_addr <= 0;
      MEM2_rs2_addr <= 0;
      MEM2_csr_rd_en <= 0;
      MEM2_pc_wdata <= 0;
    end else if (MEM1_trap.valid) begin
      MEM2_reg_wr_en <= 0;
      MEM2_result_src <= 0;
      MEM2_load_size <= 0;
      MEM2_alu_result <= 0;
      MEM2_rd_addr <= 0;
      MEM2_pc_rdata <= 0;
      MEM2_pc_plus_4 <= 0;
      MEM2_prev_trap <= MEM1_trap;
      MEM2_insn <= NOP_INSTRUCTION;
      MEM2_csr_addr <= 0;
      MEM2_csr_wr_operand <= 0;
      MEM2_csr_wr_type <= 0;
      MEM2_valid_insn <= 1;
      MEM2_intr <= 0;
      MEM2_rs1_rdata <= 0;
      MEM2_rs2_rdata <= 0;
      MEM2_rs1_addr <= 0;
      MEM2_rs2_addr <= 0;
      MEM2_csr_rd_en <= 0;
      MEM2_pc_wdata <= 0;
    end else begin
      MEM2_reg_wr_en <= MEM1_reg_wr_en;
      MEM2_result_src <= MEM1_result_src;
      MEM2_load_size <= MEM1_load_size;
      MEM2_alu_result <= MEM1_alu_result;
      MEM2_rd_addr <= MEM1_rd_addr;
      MEM2_pc_rdata <= MEM1_pc_rdata;
      MEM2_pc_plus_4 <= MEM1_pc_plus_4;
      MEM2_prev_trap <= MEM1_trap;
      MEM2_insn <= MEM1_insn;
      MEM2_csr_addr <= MEM1_csr_addr;
      MEM2_csr_wr_operand <= MEM1_csr_wr_operand;
      MEM2_csr_wr_type <= MEM1_csr_wr_type;
      MEM2_valid_insn <= MEM1_valid_insn;
      MEM2_intr <= MEM1_intr;
      MEM2_rs1_rdata <= MEM1_rs1_rdata;
      MEM2_rs2_rdata <= MEM1_rs2_rdata;
      MEM2_rs1_addr <= MEM1_rs1_addr;
      MEM2_rs2_addr <= MEM1_rs2_addr;
      MEM2_csr_rd_en <= MEM1_csr_rd_en;
      MEM2_pc_wdata <= MEM1_pc_wdata;
      MEM2_mem_wdata <= MEM1_mem_wdata;
      MEM2_mem_wmask <= MEM1_mem_wmask;
    end
  end
  //MEM2/WB
  always_ff @(posedge clk_i) begin
    if (rst_i || WB_flush) begin
      WB_reg_wr_en_int <= 0;
      WB_rd_addr_int <= 0;
      WB_insn <= NOP_INSTRUCTION;
      WB_alu_result <= 0;
      WB_mem_rdata <= 0;
      WB_pc_rdata <= 0;
      WB_pc_plus_4 <= 0;
      WB_result_src <= 0;
      WB_prev_trap <= '{default: 0};
      WB_csr_addr <= 0;
      WB_csr_wr_operand <= 0;
      WB_csr_wr_type_int <= 0;
      WB_valid_insn <= 0;
      WB_intr <= 0;
      WB_rs1_rdata <= 0;
      WB_rs2_rdata <= 0;
      WB_rs1_addr <= 0;
      WB_rs2_addr <= 0;
      WB_mem_rdata <= 0;
      WB_mem_rmask <= 0;
      WB_mem_wdata <= 0;
      WB_mem_wmask <= 0;
      WB_csr_rd_en_int <= 0;
      WB_pc_wdata <= 0;
    end else if (MEM2_trap.valid) begin
      WB_reg_wr_en_int <= 0;
      WB_rd_addr_int <= 0;
      WB_insn <= NOP_INSTRUCTION;
      WB_alu_result <= 0;
      WB_mem_rdata <= 0;
      WB_pc_rdata <= 0;
      WB_pc_plus_4 <= 0;
      WB_result_src <= 0;
      WB_prev_trap <= MEM2_trap;
      WB_csr_addr <= 0;
      WB_csr_wr_operand <= 0;
      WB_csr_wr_type_int <= 0;
      WB_valid_insn <= 1;
      WB_intr <= 0;
      WB_rs1_rdata <= 0;
      WB_rs2_rdata <= 0;
      WB_rs1_addr <= 0;
      WB_rs2_addr <= 0;
      WB_mem_rdata <= 0;
      WB_mem_rmask <= 0;
      WB_mem_wdata <= 0;
      WB_mem_wmask <= 0;
      WB_csr_rd_en_int <= 0;
      WB_pc_wdata <= 0;
    end else begin
      WB_reg_wr_en_int <= MEM2_reg_wr_en;
      WB_rd_addr_int <= MEM2_rd_addr;
      WB_insn <= MEM2_insn;
      WB_alu_result <= MEM2_alu_result;
      WB_mem_rdata <= MEM2_mem_rdata;
      WB_pc_rdata <= MEM2_pc_rdata;
      WB_pc_plus_4 <= MEM2_pc_plus_4;
      WB_result_src <= MEM2_result_src;
      WB_prev_trap <= MEM2_trap;
      WB_csr_addr <= MEM2_csr_addr;
      WB_csr_wr_operand <= MEM2_csr_wr_operand;
      WB_csr_wr_type_int <= MEM2_csr_wr_type;
      WB_valid_insn <= MEM2_valid_insn;
      WB_intr <= MEM2_intr;
      WB_rs1_rdata <= MEM2_rs1_rdata;
      WB_rs2_rdata <= MEM2_rs2_rdata;
      WB_rs1_addr <= MEM2_rs1_addr;
      WB_rs2_addr <= MEM2_rs2_addr;
      WB_mem_rdata <= MEM2_mem_rdata;
      WB_mem_rmask <= MEM2_mem_rmask;
      WB_mem_wdata <= MEM2_mem_wdata;
      WB_mem_wmask <= MEM2_mem_wmask;
      WB_csr_rd_en_int <= MEM2_csr_rd_en;
      WB_pc_wdata <= MEM2_pc_wdata;
    end
  end

  //////////////////////////////////////
  //
  //  TRAP HANDLING
  //
  //
  ///////////////////////////////////////

  // trap logic
  logic misaligned_imem_addr;
  assign misaligned_imem_addr = IF_pc_tick[1] | IF_pc_tick[0];
  always_comb begin
    if (misaligned_imem_addr) begin  // properly aligned instruction address
      IF_trap = '{1, 0, 0, TRAP_CODE_INSTR_ADDR_MISALIGNED, IF_pc_tick};
    end else begin  // misaligned instruction address triggerst a trap
      IF_trap = '{default: 0};
    end
  end

  // determine if the instruction generates a trap
  always_comb begin
    if (ID_is_ecall) begin
      ID_trap = '{1, 0, ID_insn, TRAP_CODE_ECALL_M_MODE, ID_pc_rdata};
    end else if (ID_is_ebreak) begin
      ID_trap = '{1, 0, ID_insn, TRAP_CODE_BREAKPOINT, ID_pc_rdata};
    end else if (ID_unknown_insn) begin
      ID_trap = '{1, 0, ID_insn, TRAP_CODE_ILLEGAL_INSTR, ID_pc_rdata};
    end else if (ID_prev_trap.valid) begin
      ID_trap = ID_prev_trap;
    end else begin
      ID_trap = '{default: 0};
    end
  end

  assign EX_trap = EX_prev_trap.valid ? EX_prev_trap : EX_misaligned_jump_or_branch ?
      '{1, 0, EX_insn, TRAP_CODE_INSTR_ADDR_MISALIGNED, EX_pc_rdata} :
      '{default: 0};

  always_comb begin
    if (MEM1_prev_trap.valid) begin
      MEM1_trap = MEM1_prev_trap;
    end else if (MEM1_store_trap_valid) begin
      MEM1_trap = '{1, 0, MEM1_insn, MEM1_store_trap_code, MEM1_pc_rdata};
    end else begin
      MEM1_trap = '{default: 0};
    end
  end

  always_comb begin
    if (MEM2_prev_trap.valid) begin
      MEM2_trap = MEM2_prev_trap;
    end else if (MEM2_load_trap_valid) begin
      MEM2_trap = '{1, 0, MEM2_insn, MEM2_load_trap_code, MEM2_pc_rdata};
    end else begin
      MEM2_trap = '{default: 0};
    end
  end

  assign WB_trap = WB_prev_trap.valid ? WB_prev_trap : '{default: 0};

  //////////////////////////////////////
  //
  //  HAZARD LOGIC
  //
  //
  ///////////////////////////////////////

  dtcore32_hazard_unit dtcore32_hazard_unit_inst (
      .EX_rs1_addr_i(EX_rs1_addr),
      .EX_rs2_addr_i(EX_rs2_addr),
      .MEM1_rd_addr_i(MEM1_rd_addr),
      .MEM2_rd_addr_i(MEM2_rd_addr),
      .WB_rd_addr_i(WB_rd_addr),
      .MEM2_result_src_i(MEM2_result_src),
      .EX_result_src_i(EX_result_src),
      .ID_rs1_addr_i(ID_rs1_addr),
      .ID_rs2_addr_i(ID_rs2_addr),
      .EX_rd_addr_i(EX_rd_addr),
      .EX_pc_src_i(EX_pc_src),
      .EX_forward_a_o(EX_forward_a),
      .EX_forward_b_o(EX_forward_b),
      .ID_forward_a_o(ID_forward_a),
      .ID_forward_b_o(ID_forward_b),
      .ID_flush_o(ID_flush),
      .EX_flush_o(EX_flush),
      .MEM1_flush_o(MEM1_flush),
      .MEM2_flush_o(MEM2_flush),
      .WB_flush_o(WB_flush),
      .IF_stall_o(IF_stall),
      .ID_stall_o(ID_stall),
      .ID_trap_valid_i(ID_trap.valid),
      .EX_trap_valid_i(EX_trap.valid),
      .MEM1_trap_valid_i(MEM1_trap.valid),
      .MEM2_trap_valid_i(MEM2_trap.valid),
      .WB_trap_valid_i(WB_trap.valid)
  );

  //////////////////////////////////////
  //
  //  CSRS FOR MACHINE MODE
  //
  //
  ///////////////////////////////////////

  always_comb begin
    is_csr_mstatus = 0;
    is_csr_misa = 0;
    is_csr_mie = 0;
    is_csr_mtvec = 0;
    is_csr_mscratch = 0;
    is_csr_mepc = 0;
    is_csr_mcause = 0;
    is_csr_mtval = 0;
    is_csr_mip = 0;
    is_csr_mcycle = 0;
    is_csr_mcycleh = 0;
    is_csr_minstret = 0;
    is_csr_minstreth = 0;
    is_csr_mvendorid = 0;
    is_csr_marchid = 0;
    is_csr_mimpid = 0;
    is_csr_mhartid = 0;
    is_csr_mconfigptr = 0;
    case (WB_csr_addr)
      12'h300: is_csr_mstatus = 1;
      12'h301: is_csr_misa = 1;
      12'h304: is_csr_mie = 1;
      12'h305: is_csr_mtvec = 1;
      12'h340: is_csr_mscratch = 1;
      12'h341: is_csr_mepc = 1;
      12'h342: is_csr_mcause = 1;
      12'h343: is_csr_mtval = 1;
      12'h344: is_csr_mip = 1;
      12'hB00: is_csr_mcycle = 1;
      12'hb80: is_csr_mcycleh = 1;
      12'hB02: is_csr_minstret = 1;
      12'hb82: is_csr_minstreth = 1;
      12'hf11: is_csr_mvendorid = 1;
      12'hf12: is_csr_marchid = 1;
      12'hf13: is_csr_mimpid = 1;
      12'hf14: is_csr_mhartid = 1;
      12'hf15: is_csr_mconfigptr = 1;
      default: ;
    endcase
  end

  


  assign DMEM_addr_o  = MEM1_alu_result;
  assign IMEM_addr_o  = IF_pc_rdata;
  assign DMEM_wdata_o = MEM1_mem_wdata;
  assign DMEM_wmask_o = MEM1_mem_wmask;

  //////////////////////////////////////
  //
  //  FORMAL VERIFICATION
  //
  //
  ///////////////////////////////////////

`ifdef RISCV_FORMAL

  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      rvfi_valid <= 0;
      rvfi_order <= 0;
      rvfi_insn <= 0;
      rvfi_trap <= 0;
      rvfi_halt <= 0;
      rvfi_intr <= 0;
      rvfi_mode <= 3;
      rvfi_ixl <= 1;

      rvfi_rs1_addr <= 0;
      rvfi_rs2_addr <= 0;
      rvfi_rs1_rdata <= 0;
      rvfi_rs2_rdata <= 0;

      rvfi_rd_addr <= 0;
      rvfi_rd_wdata <= 0;

      rvfi_pc_rdata <= 0;
      rvfi_pc_wdata <= 0;

      rvfi_mem_addr <= 0;
      rvfi_mem_rmask <= 0;
      rvfi_mem_wmask <= 0;
      rvfi_mem_rdata <= 0;
      rvfi_mem_wdata <= 0;

      rvfi_csr_mcycle_rmask <= 0;
      rvfi_csr_mcycle_wmask <= 0;
      rvfi_csr_mcycle_rdata <= 0;
      rvfi_csr_mcycle_wdata <= 0;

      rvfi_csr_minstret_rmask <= 0;
      rvfi_csr_minstret_wmask <= 0;
      rvfi_csr_minstret_rdata <= 0;
      rvfi_csr_minstret_wdata <= 0;

      rvfi_csr_mcause_rmask <= 0;
      rvfi_csr_mcause_wmask <= 0;
      rvfi_csr_mcause_rdata <= 0;
      rvfi_csr_mcause_wdata <= 0;

      rvfi_csr_mtvec_rmask <= 0;
      rvfi_csr_mtvec_wmask <= 0;
      rvfi_csr_mtvec_rdata <= 0;
      rvfi_csr_mtvec_wdata <= 0;

      rvfi_csr_mepc_rmask <= 0;
      rvfi_csr_mepc_wmask <= 0;
      rvfi_csr_mepc_rdata <= 0;
      rvfi_csr_mepc_wdata <= 0;
    end else begin
      rvfi_valid <= WB_valid_insn;
      if (WB_valid_insn) rvfi_order <= rvfi_order + 1;
      rvfi_insn <= (WB_trap.valid) ? WB_trap.insn : WB_insn;
      rvfi_trap <= WB_trap.valid;
      rvfi_halt <= 0;
      rvfi_intr <= WB_intr;
      rvfi_mode <= 3;
      rvfi_ixl <= 1;

      rvfi_rs1_addr <= WB_rs1_addr;
      rvfi_rs2_addr <= WB_rs2_addr;
      rvfi_rs1_rdata <= WB_rs1_rdata;
      rvfi_rs2_rdata <= WB_rs2_rdata;

      rvfi_rd_addr <= WB_rd_addr;
      rvfi_rd_wdata <= WB_rd_wdata;

      rvfi_pc_rdata <= (WB_trap.valid) ? WB_trap.pc : WB_pc_rdata;
      rvfi_pc_wdata <= WB_trap.valid   ? exception_handler_addr :
                       WB_valid_insn  ? WB_pc_wdata :
                       MEM2_valid_insn ? MEM2_pc_rdata :
                       MEM1_valid_insn ? MEM1_pc_rdata :
                       EX_valid_insn  ? EX_pc_rdata :
                       ID_valid_insn  ? ID_pc_rdata :
                       IF_valid_insn  ? IF_pc_rdata :
                       0;

      rvfi_mem_addr <= WB_alu_result;
      rvfi_mem_rmask <= WB_mem_rmask;
      rvfi_mem_wmask <= WB_mem_wmask;
      rvfi_mem_rdata <= WB_mem_rdata;
      rvfi_mem_wdata <= WB_mem_wdata;

      // make rmask and wmask cleared if an exception
      rvfi_csr_mcycle_wmask <= is_csr_mcycleh ? {WB_csr_wmask, 32'd0} : 
                                 is_csr_mcycle  ? {32'd0, WB_csr_wmask} : 
                                 64'd0;
      rvfi_csr_minstret_wmask <= is_csr_minstreth ? {WB_csr_wmask, 32'd0} :
                                   is_csr_minstret  ? {32'd0, WB_csr_wmask} : 
                                   64'd0;
      rvfi_csr_mcause_wmask <= is_csr_mcause ? WB_csr_wmask : 32'd0;
      rvfi_csr_mepc_wmask <= is_csr_mepc ? WB_csr_wmask : 32'd0;
      rvfi_csr_mtvec_wmask <= is_csr_mtvec ? WB_csr_wmask : 32'd0;
      // csr rmask logic
      rvfi_csr_mcycle_rmask <= is_csr_mcycleh ? {WB_csr_rmask, 32'd0} : 
                                 is_csr_mcycle  ? {32'd0, WB_csr_rmask} : 
                                 64'd0;
      rvfi_csr_minstret_rmask <= is_csr_minstreth ?  {WB_csr_rmask, 32'd0} : 
                                   is_csr_minstret  ? {32'd0, WB_csr_rmask} : 
                                   64'd0;
      rvfi_csr_mcause_rmask <= is_csr_mcause ? WB_csr_rmask : 32'd0;
      rvfi_csr_mtvec_rmask <= is_csr_mtvec ? WB_csr_rmask : 32'd0;
      rvfi_csr_mepc_rmask <= is_csr_mepc ? WB_csr_rmask : 32'd0;

      rvfi_csr_mcycle_rdata <= is_csr_mcycleh ? {WB_csr_rdata, 32'd0} :
                               is_csr_mcycle  ? {32'd0, WB_csr_rdata} :
                               64'd0;
      rvfi_csr_minstret_rdata <= is_csr_minstreth ? {WB_csr_rdata, 32'd0} :
                                 is_csr_minstret  ? {32'd0, WB_csr_rdata} :
                                 64'd0;
      // csr rdata logic
      rvfi_csr_mcause_rdata <= is_csr_mcause ? WB_csr_rdata : 32'd0;
      rvfi_csr_mtvec_rdata <= is_csr_mtvec ? WB_csr_rdata : 32'd0;
      rvfi_csr_mepc_rdata <= is_csr_mepc ? WB_csr_rdata : 32'd0;

      rvfi_csr_mcycle_wdata <= is_csr_mcycleh ? {WB_csr_wdata, 32'd0} :
                               is_csr_mcycle  ? {32'd0, WB_csr_wdata} :
                               64'd0;
      rvfi_csr_minstret_wdata <= is_csr_minstreth ? {WB_csr_wdata, 32'd0} :
                                 is_csr_minstret  ? {32'd0, WB_csr_wdata} :
                                 64'd0;
      rvfi_csr_mcause_wdata <= is_csr_mcause ? WB_csr_wdata : 32'd0;
      rvfi_csr_mtvec_wdata <= is_csr_mtvec ? WB_csr_wdata : 32'd0;
      rvfi_csr_mepc_wdata <= is_csr_mepc ? WB_csr_wdata : 32'd0;

    end
  end
`endif
endmodule
