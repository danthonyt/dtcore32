
module dtcore32 (
    input  logic        clk_i,
    input  logic        rst_i,
    input  logic [31:0] IMEM_rd_data_i,
    input  logic [31:0] DMEM_rd_data_i,
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

    output logic [31:0] rvfi_csr_mcycle_rmask,
    output logic [31:0] rvfi_csr_mcycle_wmask,
    output logic [31:0] rvfi_csr_mcycle_rdata,
    output logic [31:0] rvfi_csr_mcycle_wdata,

    output logic [31:0] rvfi_csr_minstret_rmask,
    output logic [31:0] rvfi_csr_minstret_wmask,
    output logic [31:0] rvfi_csr_minstret_rdata,
    output logic [31:0] rvfi_csr_minstret_wdata,
`endif
    output logic [31:0] IMEM_addr_o,
    output logic [31:0] DMEM_addr_o,
    output logic [31:0] DMEM_wr_data_o,
    output logic [ 3:0] DMEM_wr_byte_en_o
);
  /////////////////////////////////////////////
  //
  //  LOCAL PARAMETERS
  //
  //
  ////////////////////////////////////////////

  localparam logic [3:0] ADD_ALU_CONTROL = 4'h0;
  localparam logic [3:0] SUB_ALU_CONTROL = 4'h1;
  localparam logic [3:0] AND_ALU_CONTROL = 4'h2;
  localparam logic [3:0] OR_ALU_CONTROL = 4'h3;
  localparam logic [3:0] L_SHIFT_ALU_CONTROL = 4'h4;
  localparam logic [3:0] LT_ALU_CONTROL = 4'h5;
  localparam logic [3:0] LTU_ALU_CONTROL = 4'h6;
  localparam logic [3:0] XOR_ALU_CONTROL = 4'h7;
  localparam logic [3:0] R_SHIFT_A_ALU_CONTROL = 4'h8;
  localparam logic [3:0] R_SHIFT_L_ALU_CONTROL = 4'h9;
  localparam logic [3:0] BNE_ALU_CONTROL = 4'hC;
  localparam logic [3:0] GE_ALU_CONTROL = 4'hA;
  localparam logic [3:0] GEU_ALU_CONTROL = 4'hB;
  localparam logic [3:0] NE_ALU_CONTROL = 4'hC;

  localparam logic REGFILE_WRITE_ENABLE = 1'b1;

  // extended immediate source types used by different instructions
  localparam logic [2:0] I_ALU_TYPE_IMM_SRC = 3'b000;
  localparam logic [2:0] S_TYPE_IMM_SRC = 3'b001;
  localparam logic [2:0] B_TYPE_IMM_SRC = 3'b010;
  localparam logic [2:0] J_TYPE_IMM_SRC = 3'b011;
  localparam logic [2:0] I_SHIFT_TYPE_IMM_SRC = 3'b100;
  localparam logic [2:0] U_TYPE_IMM_SRC = 3'b101;
  localparam logic [2:0] CSR_TYPE_IMM_SRC = 3'b110;

  //ID_alu_a_src
  localparam logic [1:0] ALU_A_SRC_SELECT_REG_DATA = 2'b00;
  localparam logic [1:0] ALU_A_SRC_SELECT_ZERO = 2'b01;
  localparam logic [1:0] ALU_A_SRC_SELECT_PC = 2'b10;

  //ID_alu_b_src
  localparam logic ALU_B_SRC_SELECT_REG_DATA = 1'b0;
  localparam logic ALU_B_SRC_SELECT_IMM = 1'b1;

  //ID_mem_wr_size
  localparam logic [1:0] MEM_NO_DMEM_WR = 2'h0;
  localparam logic [1:0] MEM_WORD_WR = 2'h1;
  localparam logic [1:0] MEM_HALF_WR = 2'h2;
  localparam logic [1:0] MEM_BYTE_WR = 2'h3;

  //ID_result_src
  localparam logic [1:0] RESULT_SRC_SELECT_ALU_RESULT = 2'b00;
  localparam logic [1:0] RESULT_SRC_SELECT_DMEM_RD_DATA = 2'b01;
  localparam logic [1:0] RESULT_SRC_SELECT_NEXT_INSTR_ADDR = 2'b10;
  localparam logic [1:0] RESULT_SRC_SELECT_CSR_READ_DATA = 2'b11;

  //ID_branch
  localparam logic IS_BRANCH_INSTR = 1'b1;
  localparam logic IS_NOT_BRANCH_INSTR = 1'b0;

  //ID_alu_op
  localparam logic [1:0] ALU_OP_ILOAD_S_U_TYPE = 2'b00;
  localparam logic [1:0] ALU_OP_B_TYPE = 2'b01;
  localparam logic [1:0] ALU_OP_IALU_ISHIFT_R_TYPE = 2'b10;

  //ID_jump
  localparam logic IS_JUMP_INSTR = 1'b1;
  localparam logic IS_NOT_JUMP_INSTR = 1'b0;

  //ID_load_size
  localparam logic [2:0] DMEM_LOAD_SIZE_NO_LOAD = 3'b000;
  localparam logic [2:0] DMEM_LOAD_SIZE_WORD = 3'b000;
  localparam logic [2:0] DMEM_LOAD_SIZE_HALF = 3'b011;
  localparam logic [2:0] DMEM_LOAD_SIZE_HALFU = 3'b100;
  localparam logic [2:0] DMEM_LOAD_SIZE_BYTE = 3'b001;
  localparam logic [2:0] DMEM_LOAD_SIZE_BYTEU = 3'b010;

  //ID_pc_target_alu_src
  localparam logic PC_TARGET_ALU_SRC_SELECT_PC = 1'b0;
  localparam logic PC_TARGET_ALU_SRC_SELECT_REG_DATA = 1'b1;

  // ID_csr_wr_type
  localparam logic [1:0] CSR_WRITE_DISABLE = 2'b00;
  localparam logic [1:0] CSR_WRITE_RAW_VALUE = 2'b01;
  localparam logic [1:0] CSR_WRITE_SET_BIT_MASK = 2'b10;
  localparam logic [1:0] CSR_WRITE_CLEAR_BIT_MASK = 2'b11;

  // ID_csr_wr_operand_src
  localparam logic CSR_SRC_SELECT_REG_DATA = 1'b0;
  localparam logic CSR_SRC_SELECT_IMM = 1'b1;

  // OPCODES
  localparam logic [6:0] OPCODE_LOAD = 7'b0000011;
  localparam logic [6:0] OPCODE_STORE = 7'b0100011;
  localparam logic [6:0] OPCODE_R_TYPE = 7'b0110011;
  localparam logic [6:0] OPCODE_B_TYPE = 7'b1100011;
  localparam logic [6:0] OPCODE_I_TYPE = 7'b0010011;
  localparam logic [6:0] OPCODE_JAL = 7'b1101111;
  localparam logic [6:0] OPCODE_U_TYPE_LUI = 7'b0110111;
  localparam logic [6:0] OPCODE_U_TYPE_AUIPC = 7'b0010111;
  localparam logic [6:0] OPCODE_JALR = 7'b1100111;
  localparam logic [6:0] OPCODE_SYSCALL_CSR = 7'b1110011;
  // FUNCT3
  localparam logic [2:0] FUNCT3_LB = 3'b000;
  localparam logic [2:0] FUNCT3_LH = 3'b001;
  localparam logic [2:0] FUNCT3_LW = 3'b010;
  localparam logic [2:0] FUNCT3_LBU = 3'b100;
  localparam logic [2:0] FUNCT3_LHU = 3'b101;

  localparam logic [2:0] FUNCT3_SB = 3'b000;
  localparam logic [2:0] FUNCT3_SH = 3'b001;
  localparam logic [2:0] FUNCT3_SW = 3'b010;

  localparam logic [2:0] FUNCT3_BEQ = 3'b000;
  localparam logic [2:0] FUNCT3_BNE = 3'b001;
  localparam logic [2:0] FUNCT3_BLT = 3'b100;
  localparam logic [2:0] FUNCT3_BGE = 3'b101;
  localparam logic [2:0] FUNCT3_BLTU = 3'b110;
  localparam logic [2:0] FUNCT3_BGEU = 3'b111;

  localparam logic [2:0] FUNCT3_ADD_SUB = 3'b000;
  localparam logic [2:0] FUNCT3_SLL = 3'b001;
  localparam logic [2:0] FUNCT3_SLT = 3'b010;
  localparam logic [2:0] FUNCT3_SLTU_SLTIU = 3'b011;
  localparam logic [2:0] FUNCT3_XOR = 3'b100;
  localparam logic [2:0] FUNCT3_SRA_SRL = 3'b101;
  localparam logic [2:0] FUNCT3_OR = 3'b110;
  localparam logic [2:0] FUNCT3_AND = 3'b111;

  localparam logic [2:0] FUNCT3_ECALL_EBREAK = 3'b000;

  localparam logic [2:0] FUNCT3_CSRRW = 3'b001;
  localparam logic [2:0] FUNCT3_CSRRS = 3'b010;
  localparam logic [2:0] FUNCT3_CSRRC = 3'b011;
  localparam logic [2:0] FUNCT3_CSRRWI = 3'b101;
  localparam logic [2:0] FUNCT3_CSRRSI = 3'b110;
  localparam logic [2:0] FUNCT3_CSRRCI = 3'b111;


  localparam logic [31:0] NOP_INSTRUCTION = 32'h00000013;  // addi x0, x0, 0

  ///////////////////////////////////////////////
  //
  //  SIGNAL DECLARATIONS
  //
  //
  ///////////////////////////////////////////////

  // IMEM AND DMEM SIGNALS
  logic [31:0] DMEM_addr_int;
  logic [31:0] DMEM_wr_data_int;
  logic [ 3:0] DMEM_wr_byte_en_int;
  assign DMEM_addr_int = MEM_alu_result;
  assign DMEM_addr_o = DMEM_addr_int;
  assign IMEM_addr_o = IF_pc;
  assign DMEM_wr_data_o = DMEM_wr_data_int;
  assign DMEM_wr_byte_en_o = DMEM_wr_byte_en_int;
  // hazard unit signals
  // stops signals from propagating through the pipeline
  logic IF_stall;
  logic ID_stall;
  logic EX_stall;
  logic MEM_stall;
  logic WB_stall;

  // resets the pipeline to control signals of a NOP instruction
  logic ID_flush;
  logic EX_flush;
  logic MEM_flush;

  logic [31:0] IF_pc_tick;

  // instruction memory address of the instruction in the respective pipeline stage
  logic [31:0] IF_pc;
  logic [31:0] ID_pc;
  logic [31:0] EX_pc;
  logic [31:0] MEM_pc;
  logic [31:0] WB_pc;

  logic [31:0] IF_pc_plus_4;
  logic [31:0] ID_pc_plus_4;
  logic [31:0] EX_pc_plus_4;
  logic [31:0] MEM_pc_plus_4;
  logic [31:0] WB_pc_plus_4;

  logic [31:0] ID_instr;
  logic [31:0] EX_instr;
  logic [31:0] MEM_instr;
  logic [31:0] WB_instr;

  typedef struct {
    logic valid;
    logic is_interrupt;
    logic [30:0] mcause;
    logic [31:0] trap_pc;
  } trap_info_t;

  trap_info_t IF_trap;
  trap_info_t ID_trap;
  trap_info_t EX_trap;
  trap_info_t MEM_trap;
  trap_info_t WB_trap;

  trap_info_t ID_prev_trap;
  trap_info_t EX_prev_trap;
  trap_info_t MEM_prev_trap;
  trap_info_t WB_prev_trap;

  logic ID_reg_wr_en;
  logic EX_reg_wr_en;
  logic MEM_reg_wr_en;
  logic WB_reg_wr_en_int;
  logic WB_reg_wr_en;

  logic [2:0] ID_load_size;
  logic [2:0] EX_load_size;
  logic [2:0] MEM_load_size;
  logic [2:0] WB_load_size;

  logic ID_jump;
  logic EX_jump;

  logic [31:0] ID_reg_data_1;
  logic [31:0] EX_reg_data_1;
  logic [31:0] MEM_reg_data_1;
  logic [31:0] WB_reg_data_1;

  logic [31:0] ID_reg_data_2;
  logic [31:0] EX_reg_data_2;
  logic [31:0] MEM_reg_data_2;
  logic [31:0] WB_reg_data_2;

  logic [4:0] ID_src_reg_1;
  logic [4:0] EX_src_reg_1;
  logic [4:0] MEM_src_reg_1;
  logic [4:0] WB_src_reg_1;

  logic [4:0] ID_src_reg_2;
  logic [4:0] EX_src_reg_2;
  logic [4:0] MEM_src_reg_2;
  logic [4:0] WB_src_reg_2;

  // actual csr being read/written
  logic [11:0] ID_csr_addr;
  logic [11:0] EX_csr_addr;
  logic [11:0] MEM_csr_addr;
  logic [11:0] WB_csr_addr;

  // value used to write to a csr
  logic [31:0] EX_csr_wr_operand;
  logic [31:0] MEM_csr_wr_operand;
  logic [31:0] WB_csr_wr_operand;

  // 00 = no csr write, 01 = direct write, 10 = clear bitmask, 11 = set bitmask
  logic [1:0] ID_csr_wr_type;
  logic [1:0] EX_csr_wr_type;
  logic [1:0] MEM_csr_wr_type;
  logic [1:0] WB_csr_wr_type_int;
  logic [1:0] WB_csr_wr_type;

  // 0 = register data value, 1 = immediate data value
  logic [1:0] ID_result_src;
  logic [1:0] EX_result_src;
  logic [1:0] MEM_result_src;
  logic [1:0] WB_result_src;

  // 0 = register data value, 1 = immediate data value
  logic ID_csr_wr_operand_src;
  logic EX_csr_wr_operand_src;

  // extended immediate value depending on the immediate type
  logic [31:0] ID_imm_ext;
  logic [31:0] EX_imm_ext;

  // 00 = no write, 01 = word, 10 = half, 11 = byte
  logic [1:0] ID_mem_wr_size;
  logic [1:0] EX_mem_wr_size;
  logic [1:0] MEM_mem_wr_size;
  logic [1:0] WB_mem_wr_size;

  // register destination for writes
  logic [4:0] ID_dest_reg;
  logic [4:0] EX_dest_reg;
  logic [4:0] MEM_dest_reg;
  logic [4:0] WB_dest_reg;

  // result of alu operation depending on the instruction type
  logic [31:0] EX_alu_result;
  logic [31:0] MEM_alu_result;
  logic [31:0] WB_alu_result;

  // 0 = pc, 1 = register source 1 data
  logic ID_pc_target_alu_src;
  logic EX_pc_target_alu_src;

  // read data from data memory
  logic [31:0] MEM_dmem_rd_data;
  logic [31:0] WB_dmem_rd_data;

  // o = not a branch instruction, 1 = is a branch instruction
  logic ID_branch;
  logic EX_branch;

  logic [31:0] EX_dmem_wr_data;
  logic [31:0] MEM_dmem_wr_data;

  logic [3:0] ID_alu_control;
  logic [3:0] EX_alu_control;

  logic ID_dmem_read;
  logic EX_dmem_read;
  logic MEM_dmem_read;
  logic WB_dmem_read;

  logic ID_alu_b_src;
  logic EX_alu_b_src;

  logic [1:0] ID_alu_a_src;
  logic [1:0] EX_alu_a_src;

  // 0 = not an actual instruction; used for resets or flushes
  logic ID_valid_instr;
  logic EX_valid_instr;
  logic MEM_valid_instr;
  logic WB_valid_instr;

  // used for rvfi interface
  logic IF_intr;
  logic ID_intr;
  logic EX_intr;
  logic MEM_intr;
  logic WB_intr;

  // INSTRUCTION DECODE specific signals
  logic [3:0] ID_alu_control_int;
  logic ID_is_ecall;
  logic ID_is_ebreak;
  logic [2:0] ID_imm_src;
  logic [31:0] ID_imm_ext_tmp;
  logic ID_opcode_exception;
  logic [6:0] ID_op;
  logic [2:0] ID_funct3;
  logic ID_funct7b5;
  logic ID_alu_op_exception;
  logic ID_unknown_instruction;
  logic [1:0] ID_alu_op;
  logic ID_r_type_sub;
  logic ID_i_type_sub;


  // EXECUTE stage specific signals
  logic [1:0] EX_forward_a;
  logic [1:0] EX_forward_b;
  logic EX_pc_src;
  logic [31:0] EX_pc_target;
  logic [31:0] EX_src_a_tick;
  logic [31:0] EX_src_a;
  logic [31:0] EX_src_b;
  logic [31:0] EX_pc_target_src_a;
  logic EX_branch_cond;
  logic EX_result_src_b0;

  // DATA MEMORY stage specific signals
  logic MEM_misaligned_store;
  logic MEM_misaligned_load;
  logic MEM_unknown_load;

  // WRITEBACK stage specific signals
  logic [31:0] WB_csr_rd_data;  // reads the csr value before a write
  logic [31:0] WB_result;
  logic [31:0] WB_mem_rdata;
  logic [31:0] WB_mem_wdata;


  //////////////////////////////////////
  //
  //  INSTRUCTION FETCH STAGE
  //
  //
  ///////////////////////////////////////
  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      IF_pc   <= 0;
      IF_intr <= 0;
    end else if (WB_trap.valid) begin  // jump to trap handler if retired instrucion has a trap
      IF_pc   <= {csr_mtvec[31:2], 2'd0};
      IF_intr <= 1;
    end else if (!IF_stall) begin
      IF_pc   <= IF_pc_tick;
      IF_intr <= 0;
    end
  end

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
  assign IF_pc_plus_4 = IF_pc + 4;
  // trap logic
  always_comb begin
    if (~(IF_pc_tick[1] | IF_pc_tick[0])) begin  // properly aligned instruction address
      IF_trap = '{0, 0, 0, 0};
    end else begin  // misaligned instruction address triggerst a trap
      IF_trap = '{1, 0, 0, IF_pc_tick};
    end
  end

  always_ff @(posedge clk_i) begin
    if (rst_i || ID_flush) begin
      ID_instr <= NOP_INSTRUCTION;
      ID_pc <= 0;
      ID_pc_plus_4 <= 0;
      ID_prev_trap <= '{0, 0, 0, 0};
      ID_valid_instr <= 0;
      ID_intr <= 0;
    end  // allow 1 clock delay after a reset to prevent registering invalid instruction read data
    else if (!ID_stall)
    begin
      ID_instr <= IMEM_rd_data_i;
      ID_pc <= IF_pc;
      ID_pc_plus_4 <= IF_pc_plus_4;
      ID_prev_trap <= IF_trap;
      ID_valid_instr <= 1;
      ID_intr <= IF_intr;
    end
  end
  //////////////////////////////////////
  //
  //  INSTRUCTION DECODE STAGE
  //
  //
  ///////////////////////////////////////
  assign ID_op = ID_instr[6:0];
  assign ID_funct3 = ID_instr[14:12];
  assign ID_funct7b5 = ID_instr[30];
  assign ID_r_type_sub = ID_op[5] & ID_funct7b5;
  assign ID_i_type_sub = ~ID_op[5] & ID_funct7b5;
  assign ID_alu_control = ID_valid_instr ? ID_alu_control_int : 0;
  assign ID_src_reg_1 = ID_valid_instr ? ID_instr[19:15] : 0;
  assign ID_src_reg_2 = ID_valid_instr ? ID_instr[24:20] : 0;
  assign ID_dest_reg = ID_valid_instr ? ID_instr[11:7] : 0;
  assign ID_imm_ext = ID_valid_instr ? ID_imm_ext_tmp : 0;
  assign ID_csr_addr = ID_valid_instr ? ID_instr[31:20] : 0;
  assign ID_unknown_instruction = ID_opcode_exception | ID_alu_op_exception;
  // determine if the instruction generates a trap
  always_comb begin
    if (ID_is_ecall) begin
      ID_trap = '{1, 0, 11, ID_pc};
    end else if (ID_is_ebreak) begin
      ID_trap = '{1, 0, 3, ID_pc};
    end else if (ID_unknown_instruction) begin
      ID_trap = '{1, 0, 2, ID_pc};
    end else if (ID_prev_trap.valid) begin
      ID_trap = ID_prev_trap;
    end else begin
      ID_trap = '{0, 0, 0, 0};
    end
  end
  // csr
  // extend immediate to 32 bit value depending on instruction type
  always_comb begin
    case (ID_imm_src)
      //I-type ALU
      3'b000: ID_imm_ext_tmp = {{20{ID_instr[31]}}, ID_instr[31:20]};
      //S-type
      3'b001: ID_imm_ext_tmp = {{20{ID_instr[31]}}, ID_instr[31:25], ID_instr[11:7]};
      //B-type
      3'b010:
      ID_imm_ext_tmp = {{20{ID_instr[31]}}, ID_instr[7], ID_instr[30:25], ID_instr[11:8], 1'b0};
      //J-type
      3'b011:
      ID_imm_ext_tmp = {{12{ID_instr[31]}}, ID_instr[19:12], ID_instr[20], ID_instr[30:21], 1'b0};
      //I-type Shift
      3'b100: ID_imm_ext_tmp = {27'd0, ID_instr[24:20]};
      //U-type lui
      3'b101: ID_imm_ext_tmp = {ID_instr[31:12], 12'd0};
      // immediate type CSR instruction
      3'b110: ID_imm_ext_tmp = {27'd0, ID_instr[19:15]};
      default: ID_imm_ext_tmp = 0;
    endcase
  end

  // Decode the control signals for the specific instruction
  always_comb begin
    ID_is_ebreak = 0;
    ID_is_ecall = 0;
    ID_opcode_exception = 0;
    ID_dmem_read = 0;
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
        ID_dmem_read = 1;
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
        case (ID_funct3)
          FUNCT3_ECALL_EBREAK: begin
            if (ID_instr[20]) ID_is_ebreak = 1;
            else ID_is_ecall = 1;
          end
          FUNCT3_CSRRW: begin
            ID_reg_wr_en = REGFILE_WRITE_ENABLE;
            ID_result_src = RESULT_SRC_SELECT_CSR_READ_DATA;
            ID_csr_wr_type = CSR_WRITE_RAW_VALUE;
            ID_csr_wr_operand_src = CSR_SRC_SELECT_REG_DATA;
          end
          FUNCT3_CSRRS: begin
            ID_reg_wr_en = REGFILE_WRITE_ENABLE;
            ID_result_src = RESULT_SRC_SELECT_CSR_READ_DATA;
            ID_csr_wr_type = CSR_WRITE_SET_BIT_MASK;
            ID_csr_wr_operand_src = CSR_SRC_SELECT_REG_DATA;
          end
          FUNCT3_CSRRC: begin
            ID_reg_wr_en = REGFILE_WRITE_ENABLE;
            ID_result_src = RESULT_SRC_SELECT_CSR_READ_DATA;
            ID_csr_wr_type = CSR_WRITE_CLEAR_BIT_MASK;
            ID_csr_wr_operand_src = CSR_SRC_SELECT_REG_DATA;
          end
          FUNCT3_CSRRWI: begin
            ID_reg_wr_en = REGFILE_WRITE_ENABLE;
            ID_result_src = RESULT_SRC_SELECT_CSR_READ_DATA;
            ID_imm_src = CSR_TYPE_IMM_SRC;
            ID_csr_wr_type = CSR_WRITE_RAW_VALUE;
            ID_csr_wr_operand_src = CSR_SRC_SELECT_IMM;
          end
          FUNCT3_CSRRSI: begin
            ID_reg_wr_en = REGFILE_WRITE_ENABLE;
            ID_result_src = RESULT_SRC_SELECT_CSR_READ_DATA;
            ID_imm_src = CSR_TYPE_IMM_SRC;
            ID_csr_wr_type = CSR_WRITE_SET_BIT_MASK;
            ID_csr_wr_operand_src = CSR_SRC_SELECT_IMM;
          end
          FUNCT3_CSRRCI: begin
            ID_reg_wr_en = REGFILE_WRITE_ENABLE;
            ID_result_src = RESULT_SRC_SELECT_CSR_READ_DATA;
            ID_imm_src = CSR_TYPE_IMM_SRC;
            ID_csr_wr_type = CSR_WRITE_CLEAR_BIT_MASK;
            ID_csr_wr_operand_src = CSR_SRC_SELECT_IMM;
          end
          default: begin
            ID_opcode_exception = 1;
          end
        endcase
      end
      OPCODE_STORE: begin
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
        ID_reg_wr_en = REGFILE_WRITE_ENABLE;
        ID_alu_a_src = ALU_A_SRC_SELECT_REG_DATA;
        ID_alu_b_src = ALU_B_SRC_SELECT_REG_DATA;
        ID_result_src = RESULT_SRC_SELECT_ALU_RESULT;
        ID_alu_op = ALU_OP_IALU_ISHIFT_R_TYPE;
        ID_pc_target_alu_src = PC_TARGET_ALU_SRC_SELECT_PC;
      end
      OPCODE_B_TYPE: begin
        ID_imm_src = B_TYPE_IMM_SRC;
        ID_alu_a_src = ALU_A_SRC_SELECT_REG_DATA;
        ID_alu_b_src = ALU_B_SRC_SELECT_REG_DATA;
        ID_branch = IS_BRANCH_INSTR;
        ID_alu_op = ALU_OP_B_TYPE;
        ID_pc_target_alu_src = PC_TARGET_ALU_SRC_SELECT_PC;
      end
      //I-type ALU or shift
      OPCODE_I_TYPE: begin
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
        ID_reg_wr_en = REGFILE_WRITE_ENABLE;
        ID_imm_src = U_TYPE_IMM_SRC;
        ID_alu_a_src = ALU_A_SRC_SELECT_ZERO;
        ID_alu_b_src = ALU_B_SRC_SELECT_IMM;
        ID_result_src = RESULT_SRC_SELECT_ALU_RESULT;
        ID_alu_op = ALU_OP_ILOAD_S_U_TYPE;
        ID_pc_target_alu_src = PC_TARGET_ALU_SRC_SELECT_PC;
      end
      OPCODE_U_TYPE_AUIPC: begin
        ID_reg_wr_en = REGFILE_WRITE_ENABLE;
        ID_imm_src = U_TYPE_IMM_SRC;
        ID_alu_a_src = ALU_A_SRC_SELECT_PC;
        ID_alu_b_src = ALU_B_SRC_SELECT_IMM;
        ID_result_src = RESULT_SRC_SELECT_ALU_RESULT;
        ID_alu_op = ALU_OP_ILOAD_S_U_TYPE;
        ID_pc_target_alu_src = PC_TARGET_ALU_SRC_SELECT_PC;
      end
      OPCODE_JALR: begin
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
    ID_alu_control_int  = 0;
    case (ID_alu_op)
      //I-type Load, S-type, U-type
      ALU_OP_ILOAD_S_U_TYPE:
      ID_alu_control_int = ADD_ALU_CONTROL;  //add- lw,sw,lb,lh,lbu,lhu,sb,sh,auipc,lui
      //B-type
      ALU_OP_B_TYPE:
      case (ID_funct3)
        FUNCT3_BEQ:  ID_alu_control_int = SUB_ALU_CONTROL;  //sub - beq
        FUNCT3_BNE:  ID_alu_control_int = BNE_ALU_CONTROL;  //sub - bne
        FUNCT3_BLT:  ID_alu_control_int = LT_ALU_CONTROL;  //blt
        FUNCT3_BGE:  ID_alu_control_int = GE_ALU_CONTROL;  //bge
        FUNCT3_BLTU: ID_alu_control_int = LTU_ALU_CONTROL;  //bltu
        FUNCT3_BGEU: ID_alu_control_int = GEU_ALU_CONTROL;  //bgeu
        default: begin
          ID_alu_op_exception = 1;
        end
      endcase
      //R-type, I-type ALU,I-type logical shift
      ALU_OP_IALU_ISHIFT_R_TYPE:
      case (ID_funct3)
        FUNCT3_ADD_SUB:
        ID_alu_control_int = (ID_r_type_sub) ? SUB_ALU_CONTROL  /*sub*/ : ADD_ALU_CONTROL  /*add*/;
        FUNCT3_SLL: ID_alu_control_int = L_SHIFT_ALU_CONTROL;  //sll
        FUNCT3_SLT: ID_alu_control_int = LT_ALU_CONTROL;  //slt
        FUNCT3_SLTU_SLTIU: ID_alu_control_int = LTU_ALU_CONTROL;  //sltu, sltiu
        FUNCT3_XOR: ID_alu_control_int = XOR_ALU_CONTROL;  //xor
        FUNCT3_SRA_SRL:
        ID_alu_control_int = (ID_r_type_sub || ID_i_type_sub) ? R_SHIFT_A_ALU_CONTROL /*sra*/ : R_SHIFT_L_ALU_CONTROL /*srl*/;
        FUNCT3_OR: ID_alu_control_int = OR_ALU_CONTROL;  //or
        FUNCT3_AND: ID_alu_control_int = AND_ALU_CONTROL;  //and
        default: begin
          ID_alu_op_exception = 1;
        end
      endcase
      default: begin
        ID_alu_op_exception = 1;
      end
    endcase
  end
  // register file
  dtcore32_regfile dtcore32_regfile_inst (
      .clk_i(clk_i),
      .rst_i(rst_i),
      .regfile_wr_en_i(WB_reg_wr_en),
      .src_reg_1_i(ID_src_reg_1),
      .src_reg_2_i(ID_src_reg_2),
      .dest_reg_i(WB_dest_reg),
      .reg_wr_data_i(WB_result),
      .src_reg_1_rd_data_o(ID_reg_data_1),
      .src_reg_2_rd_data_o(ID_reg_data_2)
  );

  // ID/EX register
  always_ff @(posedge clk_i) begin
    if (rst_i || EX_flush) begin
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
      EX_reg_data_1 <= 0;
      EX_reg_data_2 <= 0;
      EX_pc <= 0;
      EX_src_reg_1 <= 0;
      EX_src_reg_2 <= 0;
      EX_dest_reg <= 0;
      EX_imm_ext <= 0;
      EX_pc_plus_4 <= 0;
      EX_dmem_read <= 0;
      EX_instr <= NOP_INSTRUCTION;
      EX_prev_trap <= '{0, 0, 0, 0};
      EX_csr_addr <= 0;
      EX_csr_wr_operand_src <= 0;
      EX_csr_wr_type <= 0;
      EX_valid_instr <= 0;
      EX_intr <= 0;
    end else if (!EX_stall) begin
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
      EX_reg_data_1 <= ID_reg_data_1;
      EX_reg_data_2 <= ID_reg_data_2;
      EX_pc <= ID_pc;
      EX_src_reg_1 <= ID_src_reg_1;
      EX_src_reg_2 <= ID_src_reg_2;
      EX_dest_reg <= ID_dest_reg;
      EX_imm_ext <= ID_imm_ext;
      EX_pc_plus_4 <= ID_pc_plus_4;
      EX_dmem_read <= ID_dmem_read;
      EX_instr <= ID_instr;
      EX_prev_trap <= ID_trap;
      EX_csr_addr <= ID_csr_addr;
      EX_csr_wr_operand_src <= ID_csr_wr_operand_src;
      EX_csr_wr_type <= ID_csr_wr_type;
      EX_valid_instr <= ID_valid_instr;
      EX_intr <= ID_intr;
    end
  end

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
  assign EX_pc_src = EX_jump | (EX_branch & EX_branch_cond);
  assign EX_trap   = EX_prev_trap;
  // alu input 1 data path
  // select reg 1 data or data forwarded from WB or MEM stage
  always_comb begin
    case (EX_forward_a)
      2'b00:   EX_src_a_tick = EX_reg_data_1;
      2'b01:   EX_src_a_tick = WB_result;
      2'b10:   EX_src_a_tick = MEM_alu_result;
      default: EX_src_a_tick = 0;
    endcase
  end
  // select data from first mux, zero, or pc
  always_comb begin
    case (EX_alu_a_src)
      2'b00:   EX_src_a = EX_src_a_tick;
      2'b01:   EX_src_a = 0;
      2'b10:   EX_src_a = EX_pc;
      default: EX_src_a = 0;
    endcase
  end
  // alu input 2 data path
  // select reg 2 data or data forwarded from WB or MEM stage
  always_comb begin
    case (EX_forward_b)
      2'b00:   EX_dmem_wr_data = EX_reg_data_2;
      2'b01:   EX_dmem_wr_data = WB_result;
      2'b10:   EX_dmem_wr_data = MEM_alu_result;
      default: EX_dmem_wr_data = 0;
    endcase
  end
  // select data from first mux, or extended immediate
  always_comb begin
    unique case (EX_alu_b_src)
      1'b0: EX_src_b = EX_dmem_wr_data;
      1'b1: EX_src_b = EX_imm_ext;
    endcase
  end
  // select base address for branch/jump address, selecting either
  // the current pc or reg1_data.
  always_comb begin
    unique case (EX_pc_target_alu_src)
      1'b0: EX_pc_target_src_a = EX_pc;
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
  // calculates the instruction specific alu result
  always_comb begin
    case (EX_alu_control)
      ADD_ALU_CONTROL: EX_alu_result = EX_src_a + EX_src_b;
      SUB_ALU_CONTROL: EX_alu_result = EX_src_a - EX_src_b;
      AND_ALU_CONTROL: EX_alu_result = EX_src_a & EX_src_b;
      OR_ALU_CONTROL: EX_alu_result = EX_src_a | EX_src_b;
      XOR_ALU_CONTROL: EX_alu_result = EX_src_a ^ EX_src_b;
      LT_ALU_CONTROL, LTU_ALU_CONTROL: EX_alu_result = {31'd0, EX_branch_cond};
      L_SHIFT_ALU_CONTROL: EX_alu_result = EX_src_a << EX_src_b[4:0];
      R_SHIFT_L_ALU_CONTROL: EX_alu_result = EX_src_a >> EX_src_b[4:0];
      R_SHIFT_A_ALU_CONTROL: EX_alu_result = $signed(EX_src_a) >>> EX_src_b[4:0];
      default: EX_alu_result = 0;
    endcase
  end
  // calculates the branch condition
  always_comb begin
    case (EX_alu_control)
      SUB_ALU_CONTROL: EX_branch_cond = (EX_src_a == EX_src_b) ? 1 : 0;  // beq
      NE_ALU_CONTROL: EX_branch_cond = (EX_src_a != EX_src_b) ? 1 : 0;
      LT_ALU_CONTROL: EX_branch_cond = ($signed(EX_src_a) < $signed(EX_src_b)) ? 1 : 0;
      LTU_ALU_CONTROL: EX_branch_cond = (EX_src_a < EX_src_b) ? 1 : 0;
      GE_ALU_CONTROL: EX_branch_cond = ($signed(EX_src_a) >= $signed(EX_src_b)) ? 1 : 0;
      GEU_ALU_CONTROL: EX_branch_cond = (EX_src_a >= EX_src_b) ? 1 : 0;
      default: EX_branch_cond = 0;
    endcase
  end

  // EX/MEM register
  always_ff @(posedge clk_i) begin
    if (rst_i || MEM_flush) begin
      MEM_reg_wr_en <= 0;
      MEM_result_src <= 0;
      MEM_load_size <= 0;
      MEM_mem_wr_size <= 0;
      MEM_alu_result <= 0;
      MEM_dmem_wr_data <= 0;
      MEM_dest_reg <= 0;
      MEM_pc <= 0;
      MEM_pc_plus_4 <= 0;
      MEM_prev_trap <= '{0, 0, 0, 0};
      MEM_instr <= NOP_INSTRUCTION;
      MEM_csr_addr <= 0;
      MEM_csr_wr_operand <= 0;
      MEM_csr_wr_type <= 0;
      MEM_valid_instr <= 0;
      MEM_intr <= 0;
      MEM_dmem_read <= 0;
      MEM_reg_data_1 <= 0;
      MEM_reg_data_2 <= 0;
      MEM_src_reg_1 <= 0;
      MEM_src_reg_2 <= 0;
    end else if (!MEM_stall) begin
      MEM_reg_wr_en <= EX_reg_wr_en;
      MEM_result_src <= EX_result_src;
      MEM_load_size <= EX_load_size;
      MEM_mem_wr_size <= EX_mem_wr_size;
      MEM_alu_result <= EX_alu_result;
      MEM_dmem_wr_data <= EX_dmem_wr_data;
      MEM_dest_reg <= EX_dest_reg;
      MEM_pc <= EX_pc;
      MEM_pc_plus_4 <= EX_pc_plus_4;
      MEM_prev_trap <= EX_trap;
      MEM_instr <= EX_instr;
      MEM_csr_addr <= EX_csr_addr;
      MEM_csr_wr_operand <= EX_csr_wr_operand;
      MEM_csr_wr_type <= EX_csr_wr_type;
      MEM_valid_instr <= EX_valid_instr;
      MEM_intr <= EX_intr;
      MEM_dmem_read <= EX_dmem_read;
      MEM_reg_data_1 <= EX_reg_data_1;
      MEM_reg_data_2 <= EX_reg_data_2;
      MEM_src_reg_1 <= EX_src_reg_1;
      MEM_src_reg_2 <= EX_src_reg_2;
    end
  end

  //////////////////////////////////////
  //
  //  DATA MEMORY STAGE
  //
  //
  ///////////////////////////////////////
  always_comb begin
    if (MEM_prev_trap.valid) begin
      MEM_trap = MEM_prev_trap;
    end else if (MEM_misaligned_load) begin
      MEM_trap = '{1, 0, 4, MEM_pc};
    end else if (MEM_misaligned_store) begin
      MEM_trap = '{1, 0, 6, MEM_pc};
    end else begin
      MEM_trap = '{0, 0, 0, 0};
    end
  end
  // logic to determine which bytes are written to data memory for store instructions
  always_comb begin
    MEM_misaligned_store = 0;
    DMEM_wr_data_int = 0;
    DMEM_wr_byte_en_int = 0;
    unique case (MEM_mem_wr_size)
      MEM_NO_DMEM_WR: begin
      end
      MEM_WORD_WR: begin
        DMEM_wr_data_int = MEM_dmem_wr_data;
        DMEM_wr_byte_en_int = 4'hf;
      end
      MEM_HALF_WR: begin
        case (MEM_alu_result[1:0])
          2'b00: begin
            DMEM_wr_byte_en_int = 4'h3;
            DMEM_wr_data_int = {16'd0, MEM_dmem_wr_data[15:0]};
          end
          2'b10: begin
            DMEM_wr_byte_en_int = 4'hc;
            DMEM_wr_data_int = {MEM_dmem_wr_data[15:0], 16'd0};
          end
          default: MEM_misaligned_store = 1;
        endcase

      end
      MEM_BYTE_WR: begin
        case (MEM_alu_result[1:0])
          2'b00: begin
            DMEM_wr_byte_en_int = 4'h1;
            DMEM_wr_data_int = {24'd0, MEM_dmem_wr_data[7:0]};
          end
          2'b01: begin
            DMEM_wr_byte_en_int = 4'h2;
            DMEM_wr_data_int = {16'd0, MEM_dmem_wr_data[7:0], 8'd0};
          end
          2'b10: begin
            DMEM_wr_byte_en_int = 4'h4;
            DMEM_wr_data_int = {8'd0, MEM_dmem_wr_data[7:0], 16'd0};
          end
          2'b11: begin
            DMEM_wr_byte_en_int = 4'h8;
            DMEM_wr_data_int = {MEM_dmem_wr_data[7:0], 24'd0};
          end
          default: MEM_misaligned_store = 1;
        endcase
      end
    endcase
  end

  // logic to determine which bits of the read data from data memory will be loaded for load instructions
  always_comb begin
    MEM_misaligned_load = 0;
    MEM_unknown_load = 0;
    MEM_dmem_rd_data = 0;
    case (MEM_load_size)
      //lw
      DMEM_LOAD_SIZE_WORD: begin
        MEM_dmem_rd_data = DMEM_rd_data_i;
      end
      //lb
      DMEM_LOAD_SIZE_BYTE:
      unique case (MEM_alu_result[1:0])
        2'b00: begin
          MEM_dmem_rd_data = {{24{DMEM_rd_data_i[7]}}, DMEM_rd_data_i[7:0]};
        end
        2'b01: begin
          MEM_dmem_rd_data = {{24{DMEM_rd_data_i[15]}}, DMEM_rd_data_i[15:8]};
        end
        2'b10: begin
          MEM_dmem_rd_data = {{24{DMEM_rd_data_i[23]}}, DMEM_rd_data_i[23:16]};
        end
        2'b11: begin
          MEM_dmem_rd_data = {{24{DMEM_rd_data_i[31]}}, DMEM_rd_data_i[31:24]};
        end
      endcase
      //lbu
      DMEM_LOAD_SIZE_BYTEU:
      unique case (MEM_alu_result[1:0])
        2'b00: begin
          MEM_dmem_rd_data = {{24{1'b0}}, DMEM_rd_data_i[7:0]};
        end
        2'b01: begin
          MEM_dmem_rd_data = {{24{1'b0}}, DMEM_rd_data_i[15:8]};
        end
        2'b10: begin
          MEM_dmem_rd_data = {{24{1'b0}}, DMEM_rd_data_i[23:16]};
        end
        2'b11: begin
          MEM_dmem_rd_data = {{24{1'b0}}, DMEM_rd_data_i[31:24]};
        end
      endcase
      //lh
      DMEM_LOAD_SIZE_HALF:
      case (MEM_alu_result[1:0])
        2'b00: begin
          MEM_dmem_rd_data = {{16{DMEM_rd_data_i[15]}}, DMEM_rd_data_i[15:0]};
        end
        2'b10: begin
          MEM_dmem_rd_data = {{16{DMEM_rd_data_i[31]}}, DMEM_rd_data_i[31:16]};
        end
        default: MEM_misaligned_load = 1;
      endcase

      //lhu
      DMEM_LOAD_SIZE_HALFU:
      case (MEM_alu_result[1:0])
        2'b00: begin
          MEM_dmem_rd_data = {{16{1'b0}}, DMEM_rd_data_i[15:0]};
        end
        2'b10: begin
          MEM_dmem_rd_data = {{16{1'b0}}, DMEM_rd_data_i[31:16]};
        end
        default: MEM_misaligned_load = 1;

      endcase

      default: MEM_unknown_load = 1;
    endcase
  end
  // pipeline to WB stage
  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      WB_reg_wr_en_int <= 0;
      WB_dest_reg <= 0;
      WB_instr <= NOP_INSTRUCTION;
      WB_alu_result <= 0;
      WB_dmem_rd_data <= 0;
      WB_pc <= 0;
      WB_pc_plus_4 <= 0;
      WB_result_src <= 0;
      WB_prev_trap <= '{0, 0, 0, 0};
      WB_csr_addr <= 0;
      WB_csr_wr_operand <= 0;
      WB_csr_wr_type_int <= 0;
      WB_valid_instr <= 0;
      WB_intr <= 0;
      WB_dmem_read <= 0;
      WB_reg_data_1 <= 0;
      WB_reg_data_2 <= 0;
      WB_src_reg_1 <= 0;
      WB_src_reg_2 <= 0;
      WB_mem_wr_size <= 0;
      WB_load_size <= 0;
      WB_mem_rdata <= 0;
      WB_mem_wdata <= 0;

    end else if (!WB_stall) begin
      WB_reg_wr_en_int <= MEM_reg_wr_en;
      WB_dest_reg <= MEM_dest_reg;
      WB_instr <= MEM_instr;
      WB_alu_result <= MEM_alu_result;
      WB_dmem_rd_data <= MEM_dmem_rd_data;
      WB_pc <= MEM_pc;
      WB_pc_plus_4 <= MEM_pc_plus_4;
      WB_result_src <= MEM_result_src;
      WB_prev_trap <= MEM_trap;
      WB_csr_addr <= MEM_csr_addr;
      WB_csr_wr_operand <= MEM_csr_wr_operand;
      WB_csr_wr_type_int <= MEM_csr_wr_type;
      WB_valid_instr <= MEM_valid_instr;
      WB_intr <= MEM_intr;
      WB_dmem_read <= MEM_dmem_read;
      WB_reg_data_1 <= MEM_reg_data_1;
      WB_reg_data_2 <= MEM_reg_data_2;
      WB_src_reg_1 <= MEM_src_reg_1;
      WB_src_reg_2 <= MEM_src_reg_2;
      WB_mem_wr_size <= MEM_mem_wr_size;
      WB_load_size <= MEM_load_size;
      WB_mem_rdata <= DMEM_rd_data_i;
      WB_mem_wdata <= DMEM_wr_data_int;
    end
  end

  //////////////////////////////////////
  //
  //  WRITEBACK STAGE
  //
  //
  ///////////////////////////////////////
  assign WB_reg_wr_en   = WB_reg_wr_en_int & ~WB_stall;
  assign WB_csr_wr_type = (!WB_stall) ? WB_csr_wr_type : 0;
  always_comb begin
    unique case (WB_result_src)
      2'b00: WB_result = WB_alu_result;
      2'b01: WB_result = WB_dmem_rd_data;
      2'b10: WB_result = WB_pc_plus_4;
      2'b11: WB_result = WB_csr_rd_data;
    endcase
  end
  assign WB_trap = WB_prev_trap;

  //////////////////////////////////////
  //
  //  HAZARD LOGIC
  //
  //
  ///////////////////////////////////////

  assign EX_result_src_b0 = EX_result_src[0];
  dtcore32_hazard_unit dtcore32_hazard_unit_inst (
      .clk_i(clk_i),
      .rst_i(rst_i),
      .EX_src_reg_1_i(EX_src_reg_1),
      .EX_src_reg_2_i(EX_src_reg_2),
      .MEM_dest_reg_i(MEM_dest_reg),
      .WB_dest_reg_i(WB_dest_reg),
      .MEM_reg_wr_en_i(MEM_reg_wr_en),
      .WB_reg_wr_en_i(WB_reg_wr_en),
      .EX_result_src_b0_i(EX_result_src_b0),
      .ID_src_reg_1_i(ID_src_reg_1),
      .ID_src_reg_2_i(ID_src_reg_2),
      .EX_dest_reg_i(EX_dest_reg),
      .EX_dmem_read_i(EX_dmem_read),
      .EX_pc_src_i(EX_pc_src),
      .EX_forward_a_o(EX_forward_a),
      .EX_forward_b_o(EX_forward_b),
      .ID_flush_o(ID_flush),
      .EX_flush_o(EX_flush),
      .MEM_flush_o(MEM_flush),
      .IF_stall_o(IF_stall),
      .ID_stall_o(ID_stall),
      .EX_stall_o(EX_stall),
      .MEM_stall_o(MEM_stall),
      .WB_stall_o(WB_stall),
      .EX_trap_valid_i(EX_trap.valid),
      .MEM_trap_valid_i(MEM_trap.valid),
      .WB_trap_valid_i(WB_trap.valid)
  );

  //////////////////////////////////////
  //
  //  CSRS FOR MACHINE MODE
  //
  //
  ///////////////////////////////////////

  logic [31:0] csr_mtvec;
  logic [31:0] csr_mscratch;
  logic [31:0] csr_mepc;
  logic [31:0] csr_mcause;
  logic [31:0] csr_mtval;
  logic [63:0] csr_mcycle;
  logic [63:0] csr_minstret;
  logic [31:0] csr_wr_data;
  logic [31:0] csr_current_value;

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
  logic is_csr_minstret;
  logic is_csr_mvendorid;
  logic is_csr_marchid;
  logic is_csr_mimpid;
  logic is_csr_mhartid;
  logic is_csr_mconfigptr;

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
    is_csr_minstret = 0;
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
      12'hB02: is_csr_minstret = 1;
      12'hf11: is_csr_mvendorid = 1;
      12'hf12: is_csr_marchid = 1;
      12'hf13: is_csr_mimpid = 1;
      12'hf14: is_csr_mhartid = 1;
      12'hf15: is_csr_mconfigptr = 1;
      default: ;
    endcase
  end

  always_comb begin
    // get the current csr value for write operation
    if (is_csr_mtvec) csr_current_value = csr_mtvec;
    else if (is_csr_mscratch) csr_current_value = csr_mscratch;
    else if (is_csr_mepc) csr_current_value = csr_mepc;
    else if (is_csr_mcause) csr_current_value = csr_mcause;
    else if (is_csr_mtval) csr_current_value = csr_mtval;
    else if (is_csr_mcycle) csr_current_value = csr_mcycle[31:0];
    else if (is_csr_minstret) csr_current_value = csr_minstret[31:0];
    else csr_current_value = 0;
    // then use it in the csr instruction
    case (WB_csr_wr_type)
      2'b01:   csr_wr_data = WB_csr_wr_operand;
      2'b10:   csr_wr_data = csr_current_value & ~WB_csr_wr_operand;
      2'b11:   csr_wr_data = csr_current_value | WB_csr_wr_operand;
      default: csr_wr_data = 0;
    endcase
  end

  // read the value of the CSR register selected
  always_comb begin
    if (is_csr_mtvec) WB_csr_rd_data = csr_mtvec;
    else if (is_csr_mscratch) WB_csr_rd_data = csr_mscratch;
    else if (is_csr_mepc) WB_csr_rd_data = csr_mepc;
    else if (is_csr_mcause) WB_csr_rd_data = csr_mcause;
    else if (is_csr_mtval) WB_csr_rd_data = csr_mtval;
    else if (is_csr_mcycle) WB_csr_rd_data = csr_mcycle[31:0];
    else if (is_csr_minstret) WB_csr_rd_data = csr_minstret[31:0];
    else WB_csr_rd_data = 0;
  end

  // synchronous writes
  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      csr_mepc   <= 0;
      csr_mcause <= 0;
    end else if (WB_valid_instr && WB_trap.valid) begin
      csr_mepc   <= WB_pc;
      csr_mcause <= {WB_trap.is_interrupt, WB_trap.mcause};
    end else if (is_csr_mepc) csr_mepc <= csr_wr_data;
    else if (is_csr_mcause) csr_mcause <= csr_wr_data;
  end

  // the mcycle register increments on every clock cycle
  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      csr_mcycle <= 0;
    end else if (is_csr_mcycle) begin
      csr_mcycle <= {32'd0, csr_wr_data};
    end else begin
      csr_mcycle <= csr_mcycle + 1;
    end
  end

  // the minstret register increments every time a valid instruction is retired
  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      csr_minstret <= 0;
    end else if (is_csr_minstret) begin
      csr_minstret <= {32'd0, csr_wr_data};
    end else if (WB_valid_instr) begin
      csr_minstret <= csr_minstret + 1;
    end
  end


  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      csr_mtvec <= 0;
      csr_mscratch <= 0;
    end else if (is_csr_mtvec) csr_mtvec <= csr_wr_data & 32'hffff_fffc;
    else if (is_csr_mscratch) csr_mscratch <= csr_wr_data;
  end

  //////////////////////////////////////
  //
  //  FORMAL VERIFICATION
  //
  //
  ///////////////////////////////////////

`ifdef RISCV_FORMAL

  logic [3:0] rvfi_mem_rmask_int;
  logic [3:0] rvfi_mem_wmask_int;
  logic [3:0] dmem_byte_mask;
  logic [3:0] dmem_half_mask;
  logic [3:0] dmem_word_mask;

  always_ff @(posedge clk) begin
    rvfi_valid <= WB_valid_instr & ~WB_stall;
    rvfi_order <= WB_pc;
    rvfi_insn <= WB_instr;
    rvfi_trap <= WB_trap.valid;
    rvfi_halt <= 0;
    rvfi_intr <= WB_intr;
    rvfi_mode <= 3;
    rvfi_ixl <= 1;

    rvfi_rs1_addr <= WB_src_reg_1;
    rvfi_rs2_addr <= WB_src_reg_2;
    rvfi_rs1_rdata <= WB_reg_data_1;
    rvfi_rs2_rdata <= WB_reg_data_2;

    rvfi_rd_addr <= WB_dest_reg;
    rvfi_rd_wdata <= WB_result;

    rvfi_pc_rdata <= WB_pc;
    rvfi_pc_wdata <= wb_trap.valid ? {csr_mtvec[31:2], 2'd0} : (MEM_valid_instr ? MEM_pc : (EX_valid_instr ? EX_pc : (ID_valid_instr ? ID_pc : IF_pc)));

    rvfi_mem_addr <= WB_alu_result;
    rvfi_mem_rmask <= rvfi_mem_rmask_int;
    rvfi_mem_wmask <= rvfi_mem_wmask_int;
    rvfi_mem_rdata <= WB_mem_rdata;
    rvfi_mem_wdata <= WB_mem_wdata;

    rvfi_csr_mcycle_rmask <= is_csr_mcycle ? 32'hffff_ffff : 0;
    rvfi_csr_mcycle_wmask <= is_csr_mcycle ? 32'hffff_ffff : 0;
    rvfi_csr_mcycle_rdata <= csr_current_value;
    rvfi_csr_mcycle_wdata <= csr_wr_data;

    rvfi_csr_minstret_rmask <= is_csr_minstret ? 32'hffff_ffff : 0;
    rvfi_csr_minstret_wmask <= is_csr_minstret ? 32'hffff_ffff : 0;
    rvfi_csr_minstret_rdata <= csr_current_value;
    rvfi_csr_minstret_wdata <= csr_wr_data;

  end

  always_comb begin
    dmem_word_mask = WB_dmem_read ? 4'hf : 4'h0;  // word or no load
    dmem_byte_mask = WB_alu_result[1] ? (WB_alu_result[0] ? 4'h8 : 4'h4) : (WB_alu_result[0] ? 4'h2 : 4'h1) ; // byte load
    dmem_half_mask = WB_alu_result[1] ? 4'hc : 4'h3;  // half word load
  end

  always_comb begin
    unique case (WB_load_size)
      3'b000: rvfi_mem_rmask_int = WB_dmem_read ? dmem_word_mask : 4'h0;  // word or no load
      3'b001, 3'b010: rvfi_mem_rmask_int = dmem_byte_mask;
      3'b011, 3'b100: rvfi_mem_rmask_int = dmem_half_mask;
      default: rvfi_mem_rmask_int = 0;
    endcase
  end

  always_comb begin
    unique case (WB_mem_wr_size)
      2'b00:   rvfi_mem_wmask_int = 4'h0;
      2'b01:   rvfi_mem_wmask_int = dmem_word_mask;
      2'b10:   rvfi_mem_wmask_int = dmem_half_mask;
      2'b11:   rvfi_mem_wmask_int = dmem_byte_mask;
      default: rvfi_mem_wmask_int = 4'd0;
    endcase
  end
`endif
endmodule



