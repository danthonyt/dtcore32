
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

  logic [31:0] trap_handler_addr;

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



  trap_info_t ID_trap;
  trap_info_t EX_trap;
  trap_info_t MEM1_trap;
  trap_info_t MEM2_trap;
  trap_info_t WB_trap;

  trap_info_t EX_prev_trap;
  trap_info_t MEM1_prev_trap;
  trap_info_t MEM2_prev_trap;
  trap_info_t WB_prev_trap;


  logic [2:0] ID_mem_ltype;
  logic [2:0] EX_mem_ltype;
  logic [2:0] MEM1_mem_ltype;
  logic [2:0] MEM2_mem_ltype;

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

  logic [1:0] ID_mem_stype;
  logic [1:0] EX_mem_stype;
  logic [1:0] MEM1_mem_stype;

  // register destination for writes
  logic [4:0] ID_rd_addr;
  logic [4:0] EX_rd_addr;
  logic [4:0] MEM1_rd_addr;
  logic [4:0] MEM2_rd_addr;
  logic [4:0] WB_rd_addr;

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

  logic ID_is_jalr;
  logic EX_is_jalr;


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
  logic [2:0] ID_imm_src;
  logic [6:0] ID_op;
  logic [2:0] ID_funct3;
  logic ID_funct7b5;
  logic [6:0] ID_funct7;
  logic [11:0] ID_funct12;
  logic [1:0] ID_alu_op;
  logic ID_rtype_alt;
  logic ID_itype_alt;
  logic ID_forward_a;
  logic ID_forward_b;
  logic ID_valid_rs1_addr;
  logic ID_valid_rs2_addr;
  logic ID_valid_rd_addr;
  logic [30:0] maindec_mcause;
  logic maindec_trap_valid;


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

  // DATA MEMORY stage specific signals
  logic MEM_misaligned_store;

  // WRITEBACK stage specific signals
  logic [31:0] WB_csr_rdata;  // reads the csr value before a write
  logic [31:0] WB_result;

  logic [31:0] WB_rd_wdata;

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

  assign ID_rtype_alt = ID_op[5] & ID_funct7b5;
  assign ID_itype_alt = ~ID_op[5] & ID_funct7b5;
  assign ID_rs1_addr = (ID_valid_rs1_addr) ? ID_insn[19:15] : 0;
  assign ID_rs2_addr = (ID_valid_rs2_addr) ? ID_insn[24:20] : 0;
  assign ID_rd_addr = (ID_valid_rd_addr) ? ID_insn[11:7] : 0;
  assign ID_csr_addr = (ID_valid_insn) ? ID_insn[31:20] : 0;

  // select forwarded rs1 or rs2 rdata if needed
  assign ID_rs1_rdata = ID_forward_a ? WB_rd_wdata : ID_rs1_regfile_rdata;
  assign ID_rs2_rdata = ID_forward_b ? WB_rd_wdata : ID_rs2_regfile_rdata;
  

  maindec maindec_inst (
      .op_i(ID_op),
      .funct3_i(ID_funct3),
      .funct7_i(ID_funct7),
      .funct12_i(ID_funct12),
      .rs1_addr_i(ID_rs1_addr),
      .rd_addr_i(ID_rd_addr),
      .valid_rd_addr_o(ID_valid_rd_addr),
      .valid_rs1_addr_o(ID_valid_rs1_addr),
      .valid_rs2_addr_o(ID_valid_rs2_addr),
      .imm_src_o(ID_imm_src),
      .alu_a_src_o(ID_alu_a_src),
      .alu_b_src_o(ID_alu_b_src),
      .mem_stype_o(ID_mem_stype),
      .result_src_o(ID_result_src),
      .branch_o(ID_branch),
      .alu_op_o(ID_alu_op),
      .jump_o(ID_jump),
      .pc_target_alu_src_o(ID_pc_target_alu_src),
      .mem_ltype_o(ID_mem_ltype),
      .csr_wtype_o(ID_csr_wr_type),
      .csr_write_src_o(ID_csr_wr_operand_src),
      .is_jalr_o(ID_is_jalr),
      .trap_mcause_o(maindec_mcause),
      .trap_valid_o(maindec_trap_valid)
  );

  extend extend_inst (
      .insn_i(ID_insn),
      .imm_src_i(ID_imm_src),
      .imm_ext_o(ID_imm_ext)
  );
  aludec aludec_inst (
      .alu_op_i(ID_alu_op),
      .rtype_alt_i(ID_rtype_alt),
      .itype_alt_i(ID_itype_alt),
      .funct3_i(ID_funct3),
      .alu_control_o(ID_alu_control)
  );
  // register file
  regfile regfile_inst (
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
  assign EX_pc_src    = (EX_jump | (EX_branch & EX_branch_cond));

  assign EX_pc_wdata = (EX_pc_src) ? EX_pc_target : EX_pc_plus_4;
  // trap if a jump or branch address is misaligned
  //assign EX_misaligned_jump_or_branch = EX_pc_src & (IF_pc_tick[1] | IF_pc_tick[0]);
  assign EX_misaligned_jump_or_branch = EX_pc_src & (IF_pc_tick[1] | IF_pc_tick[0]);
  // alu input 1 data path
  // select reg 1 data or data forwarded from WB or MEM stage
  always_comb begin
    case (EX_forward_a)
      FORWARD_SEL_NO_FORWARD:      EX_src_a_tick = EX_rs1_rdata_unforwarded;
      FORWARD_SEL_MEM1_ALU_RESULT: EX_src_a_tick = MEM1_alu_result;
      FORWARD_SEL_MEM2_ALU_RESULT: EX_src_a_tick = MEM2_alu_result;
      FORWARD_SEL_MEM2_MEM_RDATA:  EX_src_a_tick = MEM2_mem_rdata;
      FORWARD_SEL_WB_RESULT:       EX_src_a_tick = WB_result;
      default:                     EX_src_a_tick = 0;
    endcase
  end
  // select data from first mux, zero, or pc
  always_comb begin
    case (EX_alu_a_src)
      ALU_A_SRC_SELECT_REG_DATA: EX_src_a = EX_src_a_tick;
      ALU_A_SRC_SELECT_ZERO:     EX_src_a = 0;
      ALU_A_SRC_SELECT_PC:       EX_src_a = EX_pc_rdata;
      default:                   EX_src_a = 0;
    endcase
  end
  // alu input 2 data path
  // select reg 2 data or data forwarded from WB or MEM stage
  always_comb begin
    case (EX_forward_b)
      FORWARD_SEL_NO_FORWARD:      EX_mem_wdata_raw = EX_rs2_rdata_unforwarded;
      FORWARD_SEL_MEM1_ALU_RESULT: EX_mem_wdata_raw = MEM1_alu_result;
      FORWARD_SEL_MEM2_ALU_RESULT: EX_mem_wdata_raw = MEM2_alu_result;
      FORWARD_SEL_MEM2_MEM_RDATA:  EX_mem_wdata_raw = MEM2_mem_rdata;
      FORWARD_SEL_WB_RESULT:       EX_mem_wdata_raw = WB_result;
      default:                     EX_mem_wdata_raw = 0;
    endcase
  end
  // select data from first mux, or extended immediate
  always_comb begin
    unique case (EX_alu_b_src)
      ALU_B_SRC_SELECT_REG_DATA: EX_src_b = EX_mem_wdata_raw;
      ALU_B_SRC_SELECT_IMM:      EX_src_b = EX_imm_ext;
    endcase
  end
  // select base address for branch/jump address, selecting either
  // the current pc or reg1_data.
  always_comb begin
    unique case (EX_pc_target_alu_src)
      PC_TARGET_ALU_SRC_SELECT_PC:       EX_pc_target_src_a = EX_pc_rdata;
      PC_TARGET_ALU_SRC_SELECT_REG_DATA: EX_pc_target_src_a = EX_src_a_tick;
    endcase
  end
  // select write value to be used in a csr instruction
  always_comb begin
    unique case (EX_csr_wr_operand_src)
      CSR_SRC_SELECT_REG_DATA: EX_csr_wr_operand = EX_src_a_tick;
      CSR_SRC_SELECT_IMM:      EX_csr_wr_operand = EX_imm_ext;
    endcase
  end
  logic [31:0] EX_pc_target_int;
  assign EX_pc_target_int = EX_pc_target_src_a + EX_imm_ext;
  assign EX_pc_target     = EX_is_jalr ? (EX_pc_target_int & ~(1)) : EX_pc_target_int;

  alu alu_inst (
      .a_i(EX_src_a),
      .b_i(EX_src_b),
      .control_i(EX_alu_control),
      .branch_cond_o(EX_branch_cond),
      .result_o(EX_alu_result)
  );

  csrfile csrfile_inst (
      .clk_i(clk_i),
      .rst_i(rst_i),
      .WB_rd_addr_i(WB_rd_addr),
      .csr_addr_i(WB_csr_addr),
      .WB_valid_insn_i(WB_valid_insn),
      .WB_trap_i(WB_trap),
      .csr_wtype_i(WB_csr_wr_type),
      .csr_woperand(WB_csr_wr_operand),
      .trap_handler_addr_o(trap_handler_addr),
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
      .store_size_i(MEM1_mem_stype),
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
      .load_type(MEM2_mem_ltype),
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
  // make sure that instructions that dont write to any register address have x0 as rd and 0 as rd_wdata
  assign WB_rd_wdata = (WB_rd_addr != 0) ? WB_result : 0;
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
      IF_pc_rdata <= trap_handler_addr;
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
      ID_valid_insn <= 0;
      ID_intr <= 0;
    end else if (!ID_stall) begin
      ID_insn <= IMEM_rdata_i;
      ID_pc_rdata <= IF_pc_rdata;
      ID_pc_plus_4 <= IF_pc_plus_4;
      ID_valid_insn <= IF_valid_insn;
      ID_intr <= IF_intr;
    end
  end
  // ID/EX register
  always_ff @(posedge clk_i) begin
    if (rst_i || EX_flush || ID_stall || ID_trap.valid) begin
      EX_result_src <= 0;
      EX_mem_ltype <= 0;
      EX_mem_stype <= 0;
      EX_jump <= 0;
      EX_branch <= 0;
      EX_alu_control <= 0;
      EX_alu_a_src <= 0;
      EX_alu_b_src <= 0;
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
      EX_csr_addr <= 0;
      EX_csr_wr_operand_src <= 0;
      EX_csr_wr_type <= 0;
      EX_is_jalr <= 0;
      if (rst_i || EX_flush || ID_stall) begin
        EX_prev_trap <= '{default: 0};
        EX_valid_insn <= 0;
        EX_intr <= 0;
      end else if (ID_trap.valid) begin
        EX_prev_trap <= ID_trap;
        EX_valid_insn <= 1;
        EX_intr <= ID_intr;
      end
    end else begin
      EX_result_src <= ID_result_src;
      EX_mem_ltype <= ID_mem_ltype;
      EX_mem_stype <= ID_mem_stype;
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
      EX_is_jalr <= ID_is_jalr;
    end
  end
  // EX/MEM1 register
  always_ff @(posedge clk_i) begin
    if (rst_i || MEM1_flush || EX_trap.valid) begin
      MEM1_result_src <= 0;
      MEM1_mem_ltype <= 0;
      MEM1_mem_stype <= 0;
      MEM1_alu_result <= 0;
      MEM1_mem_wdata_raw <= 0;
      MEM1_rd_addr <= 0;
      MEM1_pc_rdata <= 0;
      MEM1_pc_plus_4 <= 0;
      MEM1_insn <= NOP_INSTRUCTION;
      MEM1_csr_addr <= 0;
      MEM1_csr_wr_operand <= 0;
      MEM1_csr_wr_type <= 0;
      MEM1_rs1_rdata <= 0;
      MEM1_rs2_rdata <= 0;
      MEM1_rs1_addr <= 0;
      MEM1_rs2_addr <= 0;
      MEM1_pc_wdata <= 0;
      if (rst_i || MEM1_flush) begin
        MEM1_prev_trap <= '{default: 0};
        MEM1_valid_insn <= 0;
        MEM1_intr <= 0;
      end else if (EX_trap.valid) begin
        MEM1_prev_trap <= EX_trap;
        MEM1_valid_insn <= 1;
        MEM1_intr <= EX_intr;
      end
    end else begin
      MEM1_result_src <= EX_result_src;
      MEM1_mem_ltype <= EX_mem_ltype;
      MEM1_mem_stype <= EX_mem_stype;
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
      MEM1_pc_wdata <= EX_pc_wdata;
    end
  end
  // MEM1/MEM2
  always_ff @(posedge clk_i) begin
    if (rst_i || MEM2_flush || MEM1_trap.valid) begin
      MEM2_result_src <= 0;
      MEM2_mem_ltype <= 0;
      MEM2_alu_result <= 0;
      MEM2_rd_addr <= 0;
      MEM2_pc_rdata <= 0;
      MEM2_pc_plus_4 <= 0;
      MEM2_insn <= NOP_INSTRUCTION;
      MEM2_csr_addr <= 0;
      MEM2_csr_wr_operand <= 0;
      MEM2_csr_wr_type <= 0;
      MEM2_rs1_rdata <= 0;
      MEM2_rs2_rdata <= 0;
      MEM2_rs1_addr <= 0;
      MEM2_rs2_addr <= 0;
      MEM2_pc_wdata <= 0;
      if (rst_i || MEM2_flush) begin
        MEM2_prev_trap <= '{default: 0};
        MEM2_valid_insn <= 0;
        MEM2_intr <= 0;
      end else if (MEM1_trap.valid) begin
        MEM2_prev_trap <= MEM1_trap;
        MEM2_valid_insn <= 1;
        MEM2_intr <= MEM1_intr;
      end
    end else begin
      MEM2_result_src <= MEM1_result_src;
      MEM2_mem_ltype <= MEM1_mem_ltype;
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
      MEM2_pc_wdata <= MEM1_pc_wdata;
      MEM2_mem_wdata <= MEM1_mem_wdata;
      MEM2_mem_wmask <= MEM1_mem_wmask;
    end
  end
  //MEM2/WB
  always_ff @(posedge clk_i) begin
    if (rst_i || WB_flush || MEM2_trap.valid) begin
      WB_rd_addr <= 0;
      WB_insn <= NOP_INSTRUCTION;
      WB_alu_result <= 0;
      WB_mem_rdata <= 0;
      WB_pc_rdata <= 0;
      WB_pc_plus_4 <= 0;
      WB_result_src <= 0;
      WB_csr_addr <= 0;
      WB_csr_wr_operand <= 0;
      WB_csr_wr_type <= 0;
      WB_rs1_rdata <= 0;
      WB_rs2_rdata <= 0;
      WB_rs1_addr <= 0;
      WB_rs2_addr <= 0;
      WB_mem_rdata <= 0;
      WB_mem_rmask <= 0;
      WB_mem_wdata <= 0;
      WB_mem_wmask <= 0;
      WB_pc_wdata <= 0;
      if (rst_i || WB_flush) begin
        WB_prev_trap <= '{default: 0};
        WB_valid_insn <= 0;
        WB_intr <= 0;
      end else if (MEM2_trap.valid) begin
        WB_prev_trap <= MEM2_trap;
        WB_valid_insn <= 1;
        WB_intr <= MEM2_intr;
      end
    end else begin
      WB_rd_addr <= MEM2_rd_addr;
      WB_insn <= MEM2_insn;
      WB_alu_result <= MEM2_alu_result;
      WB_mem_rdata <= MEM2_mem_rdata;
      WB_pc_rdata <= MEM2_pc_rdata;
      WB_pc_plus_4 <= MEM2_pc_plus_4;
      WB_result_src <= MEM2_result_src;
      WB_prev_trap <= MEM2_trap;
      WB_csr_addr <= MEM2_csr_addr;
      WB_csr_wr_operand <= MEM2_csr_wr_operand;
      WB_csr_wr_type <= MEM2_csr_wr_type;
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
      WB_pc_wdata <= MEM2_pc_wdata;
    end
  end

  //////////////////////////////////////
  //
  //  TRAP HANDLING
  //
  //
  ///////////////////////////////////////
  // determine if the instruction generates a trap
  always_comb begin
    if (maindec_trap_valid) begin
      ID_trap = '{
          valid: 1,
          is_interrupt: 0,
          insn: ID_insn,
          mcause: maindec_mcause,
          pc: ID_pc_rdata,
          next_pc: trap_handler_addr,
          rs1_addr: 0,
          rs2_addr: 0,
          rd_addr: 0,
          rs1_rdata: 0,
          rs2_rdata: 0,
          rd_wdata: 0
      };
    end else begin
      ID_trap = '{default: 0};
    end
  end

  always_comb begin
    if (EX_prev_trap.valid) begin
      EX_trap = EX_prev_trap;
    end else if (EX_misaligned_jump_or_branch) begin
      EX_trap = '{
          valid: 1,
          is_interrupt: 0,
          insn: EX_insn,
          mcause: TRAP_CODE_INSTR_ADDR_MISALIGNED,
          pc: EX_pc_rdata,
          next_pc: trap_handler_addr,
          rs1_addr: EX_rs1_addr,
          rs2_addr: EX_rs2_addr,
          rd_addr: EX_rd_addr,
          rs1_rdata: EX_rs1_rdata,
          rs2_rdata: EX_rs2_rdata,
          rd_wdata: 0
      };
    end else begin
      EX_trap = '{default: 0};
    end
  end

  always_comb begin
    if (MEM1_prev_trap.valid) begin
      MEM1_trap = MEM1_prev_trap;
    end else if (MEM1_store_trap_valid) begin
      MEM1_trap = '{
          valid: 1,
          is_interrupt: 0,
          insn: MEM1_insn,
          mcause: MEM1_store_trap_code,
          pc: MEM1_pc_rdata,
          next_pc: trap_handler_addr,
          rs1_addr: MEM1_rs1_addr,
          rs2_addr: MEM1_rs2_addr,
          rd_addr: MEM1_rd_addr,
          rs1_rdata: MEM1_rs1_rdata,
          rs2_rdata: MEM1_rs2_rdata,
          rd_wdata: 0
      };
    end else begin
      MEM1_trap = '{default: 0};
    end
  end

  always_comb begin
    if (MEM2_prev_trap.valid) begin
      MEM2_trap = MEM2_prev_trap;
    end else if (MEM2_load_trap_valid) begin
      MEM2_trap = '{
          valid: 1,
          is_interrupt: 0,
          insn: MEM2_insn,
          mcause: MEM2_load_trap_code,
          pc: MEM2_pc_rdata,
          next_pc: trap_handler_addr,
          rs1_addr: MEM2_rs1_addr,
          rs2_addr: MEM2_rs2_addr,
          rd_addr: MEM2_rd_addr,
          rs1_rdata: MEM2_rs1_rdata,
          rs2_rdata: MEM2_rs2_rdata,
          rd_wdata: 0
      };
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

  hazard_unit hazard_unit_inst (
      .EX_rs1_addr_i(EX_rs1_addr),
      .EX_rs2_addr_i(EX_rs2_addr),
      .MEM1_rd_addr_i(MEM1_rd_addr),
      .MEM2_rd_addr_i(MEM2_rd_addr),
      .WB_rd_addr_i(WB_rd_addr),
      .MEM1_result_src_i(MEM1_result_src),
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
      rvfi_mode <= 3;
      rvfi_ixl  <= 1;
      rvfi_halt <= 0;
      rvfi_trap <= WB_trap.valid;
      rvfi_intr <= WB_intr;

      if (WB_trap.valid) begin
        rvfi_insn <= WB_trap.insn;
        rvfi_rs1_addr <= WB_trap.rs1_addr;
        rvfi_rs2_addr <= WB_trap.rs2_addr;
        rvfi_rs1_rdata <= WB_trap.rs1_rdata;
        rvfi_rs2_rdata <= WB_trap.rs2_rdata;

        rvfi_rd_addr <= WB_trap.rd_addr;
        rvfi_rd_wdata <= WB_trap.rd_wdata;

        rvfi_pc_rdata <= WB_trap.pc;
        rvfi_pc_wdata <= WB_trap.next_pc;

        rvfi_mem_addr <= WB_alu_result;
        rvfi_mem_rmask <= WB_mem_rmask;
        rvfi_mem_wmask <= WB_mem_wmask;
        rvfi_mem_rdata <= WB_mem_rdata;
        rvfi_mem_wdata <= WB_mem_wdata;
      end else begin
        rvfi_insn <= WB_insn;
        rvfi_rs1_addr <= WB_rs1_addr;
        rvfi_rs2_addr <= WB_rs2_addr;
        rvfi_rs1_rdata <= WB_rs1_rdata;
        rvfi_rs2_rdata <= WB_rs2_rdata;

        rvfi_rd_addr <= WB_rd_addr;
        rvfi_rd_wdata <= WB_rd_wdata;

        rvfi_pc_rdata <= WB_pc_rdata;
        rvfi_pc_wdata <= WB_trap.valid ? trap_handler_addr : WB_pc_wdata;

        rvfi_mem_addr <= WB_alu_result;
        rvfi_mem_rmask <= WB_mem_rmask;
        rvfi_mem_wmask <= WB_mem_wmask;
        rvfi_mem_rdata <= WB_mem_rdata;
        rvfi_mem_wdata <= WB_mem_wdata;
      end


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
