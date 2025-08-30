
module dtcore32 #(
    parameter WISHBONE_ADDR_WIDTH = 32,
    parameter WISHBONE_BUS_WIDTH  = 32
) (
    input  logic                           CLK,
    input  logic                           RST,
`ifdef RISCV_FORMAL
    output logic                           rvfi_valid,
    output logic [                   63:0] rvfi_order,
    output logic [                   31:0] rvfi_insn,
    output logic                           rvfi_trap,
    output logic                           rvfi_halt,
    output logic                           rvfi_intr,
    output logic [                    1:0] rvfi_mode,
    output logic [                    1:0] rvfi_ixl,
    output logic [                    4:0] rvfi_rs1_addr,
    output logic [                    4:0] rvfi_rs2_addr,
    output logic [                   31:0] rvfi_rs1_rdata,
    output logic [                   31:0] rvfi_rs2_rdata,
    output logic [                    4:0] rvfi_rd_addr,
    output logic [                   31:0] rvfi_rd_wdata,
    output logic [                   31:0] rvfi_pc_rdata,
    output logic [                   31:0] rvfi_pc_wdata,
    output logic [                   31:0] rvfi_mem_addr,
    output logic [                    3:0] rvfi_mem_rmask,
    output logic [                    3:0] rvfi_mem_wmask,
    output logic [                   31:0] rvfi_mem_rdata,
    output logic [                   31:0] rvfi_mem_wdata,
    output logic [                   63:0] rvfi_csr_mcycle_rmask,
    output logic [                   63:0] rvfi_csr_mcycle_wmask,
    output logic [                   63:0] rvfi_csr_mcycle_rdata,
    output logic [                   63:0] rvfi_csr_mcycle_wdata,
    output logic [                   63:0] rvfi_csr_minstret_rmask,
    output logic [                   63:0] rvfi_csr_minstret_wmask,
    output logic [                   63:0] rvfi_csr_minstret_rdata,
    output logic [                   63:0] rvfi_csr_minstret_wdata,
    output logic [                   31:0] rvfi_csr_mcause_rmask,
    output logic [                   31:0] rvfi_csr_mcause_wmask,
    output logic [                   31:0] rvfi_csr_mcause_rdata,
    output logic [                   31:0] rvfi_csr_mcause_wdata,
    output logic [                   31:0] rvfi_csr_mepc_rmask,
    output logic [                   31:0] rvfi_csr_mepc_wmask,
    output logic [                   31:0] rvfi_csr_mepc_rdata,
    output logic [                   31:0] rvfi_csr_mepc_wdata,
    output logic [                   31:0] rvfi_csr_mtvec_rmask,
    output logic [                   31:0] rvfi_csr_mtvec_wmask,
    output logic [                   31:0] rvfi_csr_mtvec_rdata,
    output logic [                   31:0] rvfi_csr_mtvec_wdata,
`endif
    // wishbone master interface signals for IF stage
    // wishbone pipelined B4
    output logic [WISHBONE_ADDR_WIDTH-1:0] CPU_FETCH_WBM_ADR_O,
    input  logic [ WISHBONE_BUS_WIDTH-1:0] CPU_FETCH_WBM_DAT_I,
    output logic                           CPU_FETCH_WBM_CYC_O,
    output logic                           CPU_FETCH_WBM_STB_O,

    // wishbone master interface signals for mem stage
    // standard wishbone B4
    output logic MEM_CMD_START_O,
    output logic MEM_CMD_WE_O,
    output logic [WISHBONE_ADDR_WIDTH-1:0] MEM_CMD_ADDR_O,
    output logic [WISHBONE_BUS_WIDTH-1:0] MEM_CMD_WDATA_O,
    output logic [(WISHBONE_BUS_WIDTH/8)-1:0] MEM_CMD_SEL_O,
    input logic [WISHBONE_BUS_WIDTH-1:0] MEM_CMD_RDATA_I,
    input logic MEM_CMD_BUSY_I,
    input logic MEM_CMD_DONE_I
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

  //////////////////////////////////////
  //
  //
  //
  //
  // INSTRUCTION FETCH SIGNALS
  //
  //
  //
  //
  ///////////////////////////////////////
  logic [31:0] if_a_pc_plus_4_q;
  logic if_a_intr_d;
  logic if_a_intr_q;
  logic [31:0] next_pc;
  logic [31:0] if_b_pc_plus_4_q;
  logic if_b_intr_q;
  logic [31:0] if_b_pc_q;
  logic if_b_valid_q;
  logic [31:0] if_c_pc_plus_4_q;
  logic if_c_intr_q;
  logic [31:0] if_c_pc_q;
  logic if_c_valid_q;
  logic [31:0] if_c_insn_q;
  logic [31:0] trap_handler_addr_q;
  logic [31:0] pc_plus_4;
  logic [31:0] if_a_pc;
  logic [31:0] if_b_insn;
  logic if_a_valid_q;
  localparam START_ADDR = 32'd0;
  logic imem_buf_valid;
  logic [31:0] if_insn_buf;
  logic [31:0] if_insn;

  //////////////////////////////////////
  //
  //
  //
  //
  // INSTRUCTION DECODE SIGNALS
  //
  //
  //
  //
  ///////////////////////////////////////
  trap_info_t id_trap_d;
  logic [31:0] id_rs1_rdata_d;
  logic [31:0] id_rs1_rfile_rdata_comb;
  logic [31:0] id_rs2_rdata_d;
  logic [31:0] id_rs2_rfile_rdata_comb;
  logic [4:0] id_rs1_addr_d;
  logic [4:0] id_rs2_addr_d;
  logic [11:0] id_csr_addr_d;
  logic [31:0] id_imm_ext_d;
  logic [4:0] id_rd_addr_d;
  alu_control_t id_alu_control_d;

  // directly taken from instruction word
  logic [6:0] id_op_comb;
  logic [2:0] id_funct3_comb;
  logic id_funct7b5_comb;
  logic [6:0] id_funct7_comb;
  logic [11:0] id_funct12_comb;
  logic id_rtype_alt_comb;
  logic id_itype_alt_comb;
  logic id_forward_a_comb;
  logic id_forward_b_comb;
  logic id_rs1_valid_comb;
  logic id_rs2_valid_comb;
  logic id_rd_valid_comb;
  logic [30:0] id_maindec_mcause_comb;
  logic id_maindec_trap_valid_comb;
  mem_op_t id_mem_op_d;
  cf_op_t id_cf_op_d;
  csr_op_t id_csr_op_d;
  imm_ext_op_t id_imm_ext_op;
  alu_a_sel_t id_alu_a_sel_d;
  alu_b_sel_t id_alu_b_sel_d;
  pc_alu_sel_t id_pc_alu_sel_d;
  result_sel_t id_result_sel_d;
  csr_bitmask_sel_t id_csr_bitmask_sel_d;
  pipeline_t id_pipeline;


  //////////////////////////////////////
  //
  //
  //
  //
  // INSTRUCTION EXECUTE SIGNALS
  //
  //
  //
  //
  ///////////////////////////////////////
  trap_info_t ex_trap_d;
  logic [31:0] ex_rs1_rdata_d;
  logic [31:0] ex_rs2_rdata_d;
  logic [4:0] ex_rs1_addr_d;
  logic [4:0] ex_rs2_addr_d;
  logic [11:0] ex_csr_addr_d;
  logic [31:0] ex_csr_bitmask_comb;
  logic [2:0] ex_forward_a_sel_comb;
  logic [2:0] ex_forward_b_sel_comb;
  logic ex_is_pc_redirect;
  logic [31:0] ex_pc_target;
  logic [31:0] ex_src_a_tick_comb;
  logic [31:0] ex_src_a_comb;
  logic [31:0] ex_src_b_comb;
  logic [31:0] ex_pc_base;
  logic ex_branch_cond_comb;
  logic ex_misaligned_jump_or_branch_comb;
  logic [4:0] ex_rd_addr_d;
  logic [31:0] ex_alu_result_comb;
  logic [31:0] ex_pc_target_non_jalr;
  logic [31:0] ex_alu_csr_result_d;
  logic [31:0] ex_store_wdata_d;
  pipeline_t ex_pipeline;
  ///////////////////////////////////////
  //
  //
  //
  //
  // DATA MEMORY STAGE
  //
  //
  //
  //
  ///////////////////////////////////////
  trap_info_t mem_trap_d;
  logic [3:0] mem_load_rmask_comb;
  logic [31:0] mem_load_rdata_d;
  logic [31:0] mem_store_wdata_d;
  pipeline_t mem_pipeline;
  logic [30:0] mem_store_trap_mcause;
  logic mem_store_trap_valid;
  logic [30:0] mem_load_trap_mcause;
  logic mem_load_trap_valid;
  logic [3:0] mem_store_wmask_d;
  logic [3:0] mem_load_rmask_d;
  logic [3:0] mem_store_wmask_comb;
  logic [31:0] mem_formatted_load_rdata;
  logic mem_cmd_req;


  ///////////////////////////////////////
  //
  //
  //
  //
  // WRITEBACK SIGNALS
  //
  //
  //
  //
  ///////////////////////////////////////
  logic [4:0] wb_rd_addr_masked;
  logic [31:0] wb_rd_wdata_masked;
  logic [31:0] wb_rd_wdata_comb;
  logic [31:0] wb_csr_wmask_comb;
  logic [31:0] wb_csr_rmask_comb;
  logic [31:0] ex_csr_wdata_d;
  trap_info_t wb_trap_d;
  logic [11:0] wb_csr_addr_masked;
  pipeline_t wb_pipeline;
  // hazard unit signals
  // stops signals from propagating through the pipeline
  logic if_id_stall;
  logic id_ex_stall;
  logic ex_mem_stall;
  logic mem_wb_stall;

  // resets the pipeline to control signals of a NOP instruction
  logic if_id_flush;
  logic id_ex_flush;
  logic ex_mem_flush;
  logic mem_wb_flush;

  //////////////////////////////////////
  //
  //  INSTRUCTION FETCH STAGE
  //
  //
  ///////////////////////////////////////
  assign pc_plus_4 = CPU_FETCH_WBM_ADR_O + 4;
  // next pc logic
  assign next_pc = wb_trap_d.valid ? trap_handler_addr_q : 
  ex_is_pc_redirect ? ex_pc_target : pc_plus_4;

  assign if_a_intr_d = wb_trap_d.valid;

  always_ff @(posedge CLK) begin
    if (RST) begin
      CPU_FETCH_WBM_ADR_O <= START_ADDR;
      if_a_intr_q <= 0;
    end else if (!if_id_stall) begin
      CPU_FETCH_WBM_ADR_O <= next_pc;
      if_a_intr_q <= if_a_intr_d;
    end
  end

  always_ff @(posedge CLK) begin
    if (RST || if_id_flush) begin
      if_b_valid_q <= 0;
      if_b_pc_q <= 0;
      if_b_intr_q <= 0;
    end else if (!if_id_stall) begin
      if_b_valid_q <= 1;
      if_b_pc_q <= CPU_FETCH_WBM_ADR_O;
      if_b_intr_q <= if_a_intr_q;
    end
  end

  

  // buffer instruction fetch on stalls
  always_ff @(posedge CLK) begin
    if (RST || if_id_flush) begin
      if_insn_buf <= 0;
      imem_buf_valid <= 0;
    end else if (if_id_stall && !imem_buf_valid) begin
      if_insn_buf <= CPU_FETCH_WBM_DAT_I;
      imem_buf_valid <= 1;
    end else if (!if_id_stall) begin
      if_insn_buf <= 0;
      imem_buf_valid <= 0;
    end
  end

  assign if_insn = imem_buf_valid ? if_insn_buf : CPU_FETCH_WBM_DAT_I;
  assign CPU_FETCH_WBM_CYC_O = !if_id_stall;
  assign CPU_FETCH_WBM_STB_O = !if_id_stall;

  // goes into the if/id pipeline

  //////////////////////////////////////
  //
  //  INSTRUCTION DECODE STAGE
  //
  //
  ///////////////////////////////////////
  assign id_op_comb = id_pipeline.insn[6:0];
  assign id_funct3_comb = id_pipeline.insn[14:12];
  assign id_funct7b5_comb = id_pipeline.insn[30];
  assign id_funct7_comb = id_pipeline.insn[31:25];
  assign id_funct12_comb = id_pipeline.insn[31:20];

  assign id_rtype_alt_comb = id_op_comb[5] & id_funct7b5_comb;
  assign id_itype_alt_comb = ~id_op_comb[5] & id_funct7b5_comb;
  assign id_rs1_addr_d = (id_rs1_valid_comb) ? id_pipeline.insn[19:15] : 0;
  assign id_rs2_addr_d = (id_rs2_valid_comb) ? id_pipeline.insn[24:20] : 0;
  assign id_rd_addr_d = (id_rd_valid_comb) ? id_pipeline.insn[11:7] : 0;
  assign id_csr_addr_d = (id_csr_op_d != CSR_NONE) ? id_pipeline.insn[31:20] : 0;

  // select forwarded rs1 or rs2 rdata if needed
  assign id_rs1_rdata_d = id_forward_a_comb ? wb_rd_wdata_masked : id_rs1_rfile_rdata_comb;
  assign id_rs2_rdata_d = id_forward_b_comb ? wb_rd_wdata_masked : id_rs2_rfile_rdata_comb;

  decoder decoder_inst (
      .OP(id_op_comb),
      .FUNCT3(id_funct3_comb),
      .FUNCT7(id_funct7_comb),
      .FUNCT12(id_funct12_comb),
      .RS1_ADDR(id_rs1_addr_d),
      .RD_ADDR(id_rd_addr_d),
      .RTYPE_ALT(id_rtype_alt_comb),
      .ITYPE_ALT(id_itype_alt_comb),
      .RD_VALID(id_rd_valid_comb),
      .RS1_VALID(id_rs1_valid_comb),
      .RS2_VALID(id_rs2_valid_comb),
      .MEM_OP(id_mem_op_d),
      .CF_OP(id_cf_op_d),
      .CSR_OP(id_csr_op_d),
      .ALU_CONTROL(id_alu_control_d),
      .IMM_EXT_OP(id_imm_ext_op),
      .ALU_A_SRC(id_alu_a_sel_d),
      .ALU_B_SRC(id_alu_b_sel_d),
      .PC_ALU_SRC(id_pc_alu_sel_d),
      .RESULT_SRC(id_result_sel_d),
      .CSR_BITMASK_SEL(id_csr_bitmask_sel_d),
      .TRAP_MCAUSE(id_maindec_mcause_comb),
      .TRAP_VALID(id_maindec_trap_valid_comb)

  );

  extend extend_inst (
      .insn_i(id_pipeline.insn),
      .IMM_EXT_OP(id_imm_ext_op),
      .IMM_EXT(id_imm_ext_d)
  );

  // register file
  regfile regfile_inst (
      .clk_i(CLK),
      .rst_i(RST),
      .rs1_addr_i(id_rs1_addr_d),
      .rs2_addr_i(id_rs2_addr_d),
      .rd_addr_i(wb_rd_addr_masked),
      .reg_wr_data_i(wb_rd_wdata_masked),
      .rs1_rdata_o(id_rs1_rfile_rdata_comb),
      .rs2_rdata_o(id_rs2_rfile_rdata_comb)
  );

  logic [31:0] ex_csr_rdata_d;


  csrfile csrfile_inst (
      .CLK(CLK),
      .RST(RST),
      .WB_RD_ADDR(wb_rd_addr_masked),
      .CSR_RADDR(id_csr_addr_d),
      .CSR_WADDR(wb_csr_addr_masked),
      .CSR_WDATA(wb_pipeline.csr_wdata),
      .WB_VALID_INSN(wb_pipeline.valid),
      .WB_TRAP(wb_trap_d),
      .EX_VALID(ex_pipeline.valid),
      .MEM_VALID(mem_pipeline.valid),
      .WB_VALID(wb_pipeline.valid),
      .TRAP_HANDLER_ADDR(trap_handler_addr_q),
      .CSR_RDATA_REG(ex_csr_rdata_d),
      .CSR_RMASK(wb_csr_rmask_comb),
      .CSR_WMASK(wb_csr_wmask_comb)
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


  logic [31:0] ex_pc_wdata_d;
  assign ex_rs1_rdata_d = ex_src_a_tick_comb;
  assign ex_rs2_rdata_d = ex_store_wdata_d;


  // for rvfi
  assign ex_pc_wdata_d = (ex_is_pc_redirect) ? ex_pc_target : ex_pipeline.pc_plus_4;
  // trap if a jump or branch address is misaligned
  //assign ex_misaligned_jump_or_branch_comb = ex_is_pc_redirect & (next_pc[1] | next_pc[0]);
  assign ex_misaligned_jump_or_branch_comb = ex_is_pc_redirect & (next_pc[1] | next_pc[0]);

  assign ex_pc_target_non_jalr = (ex_pc_base + ex_pipeline.imm_ext);
  assign ex_pc_target     = (ex_pipeline.cf_op == CF_JALR) ? (ex_pc_target_non_jalr & ~(1'b1)) : ex_pc_target_non_jalr;
  assign ex_is_pc_redirect = (ex_pipeline.cf_op[0] | (ex_pipeline.cf_op[1] & ex_branch_cond_comb));

  // disable ex stage if trap propagates from previous stage
  // disable jumps, and set all register addresses to zero
  assign ex_rs1_addr_d = ex_pipeline.rs1_addr;
  assign ex_rs2_addr_d = ex_pipeline.rs2_addr;
  assign ex_rd_addr_d = ex_pipeline.rd_addr;
  assign ex_csr_addr_d = ex_pipeline.csr_addr;

  // alu input 1 data path
  // select reg 1 data or data forwarded from WB or MEM stage
  always_comb begin
    case (ex_forward_a_sel_comb)
      NO_FORWARD_SEL:             ex_src_a_tick_comb = ex_pipeline.rs1_rdata;
      FORWARD_SEL_MEM_ALU_RESULT: ex_src_a_tick_comb = mem_pipeline.alu_csr_result;
      FORWARD_SEL_WB_LOAD_RDATA:  ex_src_a_tick_comb = wb_pipeline.load_rdata;
      FORWARD_SEL_WB_ALU_RESULT:  ex_src_a_tick_comb = wb_pipeline.alu_csr_result;
      default:                    ex_src_a_tick_comb = 0;
    endcase
  end
  // select data from first mux, zero, or pc
  always_comb begin
    case (ex_pipeline.alu_a_sel)
      ALU_A_SEL_REG_DATA: ex_src_a_comb = ex_src_a_tick_comb;
      ALU_A_SEL_ZERO:     ex_src_a_comb = 0;
      ALU_A_SEL_PC:       ex_src_a_comb = ex_pipeline.pc;
      default:            ex_src_a_comb = 0;
    endcase
  end
  // alu input 2 data path
  // select reg 2 data or data forwarded from WB or MEM stage
  always_comb begin
    case (ex_forward_b_sel_comb)
      NO_FORWARD_SEL:             ex_store_wdata_d = ex_pipeline.rs2_rdata;
      FORWARD_SEL_MEM_ALU_RESULT: ex_store_wdata_d = mem_pipeline.alu_csr_result;
      FORWARD_SEL_WB_LOAD_RDATA:  ex_store_wdata_d = wb_pipeline.load_rdata;
      FORWARD_SEL_WB_ALU_RESULT:  ex_store_wdata_d = wb_pipeline.alu_csr_result;
      default:                    ex_store_wdata_d = 0;
    endcase
  end
  // select data from first mux, or extended immediate
  always_comb begin
    unique case (ex_pipeline.alu_b_sel)
      ALU_B_SEL_REG_DATA: ex_src_b_comb = ex_store_wdata_d;
      ALU_B_SEL_IMM:      ex_src_b_comb = ex_pipeline.imm_ext;
    endcase
  end
  // select base address for branch/jump address, selecting either
  // the current pc or reg1_data.
  always_comb begin
    unique case (ex_pipeline.pc_alu_sel)
      PC_ALU_SEL_PC:       ex_pc_base = ex_pipeline.pc;
      PC_ALU_SEL_REG_DATA: ex_pc_base = ex_src_a_tick_comb;
    endcase
  end
  // select write value to be used in a csr instruction
  always_comb begin
    unique case (ex_pipeline.csr_bitmask_sel)
      CSR_BITMASK_SEL_REG_DATA: ex_csr_bitmask_comb = ex_src_a_tick_comb;
      CSR_BITMASK_SEL_IMM:      ex_csr_bitmask_comb = ex_pipeline.imm_ext;
    endcase
  end

  always_comb begin
    ex_csr_wdata_d = 0;
    case (ex_pipeline.csr_op)
      CSR_WRITE: ex_csr_wdata_d = ex_csr_bitmask_comb;
      CSR_CLEAR: ex_csr_wdata_d = (ex_pipeline.csr_rdata & ~ex_csr_bitmask_comb);
      CSR_SET:   ex_csr_wdata_d = (ex_pipeline.csr_rdata | ex_csr_bitmask_comb);
      default:   ;
    endcase
  end


  assign ex_alu_csr_result_d = (ex_pipeline.csr_op != CSR_NONE) ? ex_csr_rdata_d : ex_alu_result_comb;

  alu alu_inst (
      .a_i(ex_src_a_comb),
      .b_i(ex_src_b_comb),
      .control_i(ex_pipeline.alu_control),
      .branch_cond_o(ex_branch_cond_comb),
      .result_o(ex_alu_result_comb)
  );




  ///////////////////////////////////////
  //
  //
  //
  //
  // DATA MEMORY STAGE
  //
  //
  //
  //
  ///////////////////////////////////////

  //logic [WISHBONE_BUS_WIDTH-1:0] mem_cmd_rdata;
  //logic mem_cmd_busy;

  // start a wishbone req if a memory instruction
  assign mem_cmd_req = !mem_pipeline.carried_trap.valid && (mem_pipeline.mem_op != MEM_NONE);
  // high when store instruction
  assign MEM_CMD_WE_O = mem_pipeline.mem_op[4] & mem_pipeline.mem_op[3];
  assign MEM_CMD_ADDR_O = mem_pipeline.alu_csr_result;
  assign MEM_CMD_WDATA_O = mem_pipeline.store_wdata;

  assign mem_store_wdata_d = mem_pipeline.store_wdata;
  assign mem_store_wmask_d =  (mem_pipeline.mem_op[4] & mem_pipeline.mem_op[3]) ? mem_store_wmask_comb : 0;
  assign mem_load_rdata_d = mem_formatted_load_rdata;
  assign mem_load_rmask_d = (mem_pipeline.mem_op[4] & !mem_pipeline.mem_op[3]) ? mem_load_rmask_comb : 0;

  // a wishbone request sends a start pulse
  pulse_generator pulse_generator_inst (
      .CLK_I(CLK),
      .RST_I(RST),
      .EN_I(mem_cmd_req && !MEM_CMD_DONE_I),
      .PULSE_O(MEM_CMD_START_O)
  );
  // format store data for MEM stage
  store_unit #(
      .BUS_WIDTH(WISHBONE_BUS_WIDTH)
  ) store_unit_inst (
      .MEM_OP(mem_pipeline.mem_op),
      .ADDR_LSB2(mem_pipeline.alu_csr_result[1:0]),
      .STORE_TRAP_VALID(mem_store_trap_valid),
      .STORE_TRAP_MCAUSE(mem_store_trap_mcause),
      .WSTRB(MEM_CMD_SEL_O),
      .STORE_WMASK(mem_store_wmask_comb)
  );

  load_unit load_unit_inst (
      .MEM_OP(mem_pipeline.mem_op),
      .ADDR_LSB2(mem_pipeline.alu_csr_result[1:0]),
      .RDATA_RAW(MEM_CMD_RDATA_I),
      .LOAD_TRAP_VALID(mem_load_trap_valid),
      .LOAD_TRAP_MCAUSE(mem_load_trap_mcause),
      .LOAD_RMASK(mem_load_rmask_comb),
      .LOAD_FORMATTED(mem_formatted_load_rdata)
  );


  //////////////////////////////////////
  //
  //  WRITEBACK STAGE
  //
  //
  ///////////////////////////////////////
  // trap disable logic
  assign wb_rd_addr_masked  = wb_pipeline.carried_trap.valid ? 0 : wb_pipeline.rd_addr;
  assign wb_csr_addr_masked = wb_pipeline.carried_trap.valid ? 0 : wb_pipeline.csr_addr;

  // disable register and csr writes for an excepted instruction
  // make sure that instructions that dont write to any register address have x0 as rd and 0 as rd_wdata
  assign wb_rd_wdata_masked = (wb_rd_addr_masked != 0) ? wb_rd_wdata_comb : 0;
  always_comb begin
    unique case (wb_pipeline.result_sel)
      RESULT_SEL_ALU_RESULT: wb_rd_wdata_comb = wb_pipeline.alu_csr_result;
      RESULT_SEL_MEM_DATA: wb_rd_wdata_comb = wb_pipeline.load_rdata;
      RESULT_SEL_NEXT_INSTR_ADDR: wb_rd_wdata_comb = wb_pipeline.pc_plus_4;
      RESULT_SEL_CSR_READ_DATA: wb_rd_wdata_comb = wb_pipeline.csr_rdata;
    endcase
  end

  //////////////////////////////////////
  //
  //  PIPELINE REGISTERS
  //
  //
  ///////////////////////////////////////

  //IF/ID
  always_ff @(posedge CLK) begin
    if (RST || if_id_flush) begin
      id_pipeline <= PIPELINE_T_RESET;
    end else if (!if_id_stall) begin
      if (!if_b_valid_q) begin
        id_pipeline <= PIPELINE_T_RESET;
      end else begin
        id_pipeline <= '{
            pc: if_b_pc_q,
            pc_plus_4: if_b_pc_q + 4,
            insn: if_insn,
            rs1_addr: 0,
            rs2_addr: 0,
            rd_addr: 0,
            rs1_rdata: 0,
            rs2_rdata: 0,
            imm_ext: 0,
            csr_addr: 0,
            csr_wdata: 0,
            csr_rdata: 0,
            csr_op: CSR_NONE,
            cf_op: CF_NONE,
            alu_control: ADD_ALU_CONTROL,
            result_sel: RESULT_SEL_ALU_RESULT,
            alu_a_sel: ALU_A_SEL_REG_DATA,
            alu_b_sel: ALU_B_SEL_REG_DATA,
            pc_alu_sel: PC_ALU_SEL_PC,
            csr_bitmask_sel: CSR_BITMASK_SEL_REG_DATA,
            mem_op: MEM_NONE,
            load_rmask: 0,
            store_wdata: 0,
            store_wmask: 0,
            alu_csr_result: 0,
            load_rdata: 0,
            pc_wdata: 0,
            valid: if_b_valid_q,
            intr: if_b_intr_q,
            carried_trap: '{default: 0}  // zero the struct if not used yet
        };
      end
    end
  end
  // ID/EX register
  always_ff @(posedge CLK) begin
    if (RST || id_ex_flush) begin
      ex_pipeline <= PIPELINE_T_RESET;
    end else if (!id_ex_stall) begin
      if (if_id_stall || !id_pipeline.valid) begin
        ex_pipeline <= PIPELINE_T_RESET;
      end else begin
        ex_pipeline <= '{
            pc: id_pipeline.pc,
            pc_plus_4: id_pipeline.pc_plus_4,
            insn: id_pipeline.insn,
            rs1_addr: id_rs1_addr_d,
            rs2_addr: id_rs2_addr_d,
            rd_addr: id_rd_addr_d,
            rs1_rdata: id_rs1_rdata_d,
            rs2_rdata: id_rs2_rdata_d,
            imm_ext: id_imm_ext_d,
            csr_addr: id_csr_addr_d,
            csr_wdata: 0,
            csr_rdata: 0,
            csr_op: id_csr_op_d,
            cf_op: id_cf_op_d,
            alu_control: id_alu_control_d,
            result_sel: id_result_sel_d,
            alu_a_sel: id_alu_a_sel_d,
            alu_b_sel: id_alu_b_sel_d,
            pc_alu_sel: id_pc_alu_sel_d,
            csr_bitmask_sel: id_csr_bitmask_sel_d,
            mem_op: id_mem_op_d,
            load_rmask: 0,
            store_wdata: 0,
            store_wmask: 0,
            alu_csr_result: 0,
            load_rdata: 0,
            pc_wdata: 0,
            valid: id_pipeline.valid,
            intr: id_pipeline.intr,
            carried_trap: id_trap_d
        };
      end
    end
  end
  // EX/MEM register
  always_ff @(posedge CLK) begin
    if (RST || ex_mem_flush) begin
      mem_pipeline <= PIPELINE_T_RESET;
    end else if (!ex_mem_stall) begin
      if (id_ex_stall || !ex_pipeline.valid) begin
        mem_pipeline <= PIPELINE_T_RESET;
      end else begin
        mem_pipeline <= '{
            pc: ex_pipeline.pc,
            pc_plus_4: ex_pipeline.pc_plus_4,
            insn: ex_pipeline.insn,
            rs1_addr: ex_rs1_addr_d,
            rs2_addr: ex_rs2_addr_d,
            rd_addr: ex_rd_addr_d,
            rs1_rdata: ex_src_a_tick_comb,
            rs2_rdata: ex_store_wdata_d,
            imm_ext: ex_pipeline.imm_ext,
            csr_addr: ex_csr_addr_d,
            csr_wdata: ex_csr_wdata_d,
            csr_rdata: ex_csr_rdata_d,
            csr_op: ex_pipeline.csr_op,
            cf_op: ex_pipeline.cf_op,
            alu_control: ex_pipeline.alu_control,
            result_sel: ex_pipeline.result_sel,
            alu_a_sel: ex_pipeline.alu_a_sel,
            alu_b_sel: ex_pipeline.alu_b_sel,
            pc_alu_sel: ex_pipeline.pc_alu_sel,
            csr_bitmask_sel: ex_pipeline.csr_bitmask_sel,
            mem_op: ex_pipeline.mem_op,
            load_rmask: 0,
            store_wdata: ex_store_wdata_d,
            store_wmask: 0,
            alu_csr_result: ex_alu_csr_result_d,
            load_rdata: 0,
            pc_wdata: ex_pc_wdata_d,
            valid: ex_pipeline.valid,
            intr: ex_pipeline.intr,
            carried_trap: ex_trap_d
        };
      end
    end
  end
  //MEM/WB
  always_ff @(posedge CLK) begin
    if (RST || mem_wb_flush) begin
      wb_pipeline <= PIPELINE_T_RESET;
    end else if (!mem_wb_stall) begin
      if (ex_mem_stall || !mem_pipeline.valid) begin
        wb_pipeline <= PIPELINE_T_RESET;
      end else begin
        wb_pipeline <= '{
            pc: mem_pipeline.pc,
            pc_plus_4: mem_pipeline.pc_plus_4,
            insn: mem_pipeline.insn,
            rs1_addr: mem_pipeline.rs1_addr,
            rs2_addr: mem_pipeline.rs2_addr,
            rd_addr: mem_pipeline.rd_addr,
            rs1_rdata: mem_pipeline.rs1_rdata,
            rs2_rdata: mem_pipeline.rs2_rdata,
            imm_ext: mem_pipeline.imm_ext,
            csr_addr: mem_pipeline.csr_addr,
            csr_wdata: mem_pipeline.csr_wdata,
            csr_rdata: mem_pipeline.csr_rdata,
            csr_op: mem_pipeline.csr_op,
            cf_op: mem_pipeline.cf_op,
            alu_control: mem_pipeline.alu_control,
            result_sel: mem_pipeline.result_sel,
            alu_a_sel: mem_pipeline.alu_a_sel,
            alu_b_sel: mem_pipeline.alu_b_sel,
            pc_alu_sel: mem_pipeline.pc_alu_sel,
            csr_bitmask_sel: mem_pipeline.csr_bitmask_sel,
            mem_op: mem_pipeline.mem_op,
            load_rmask: mem_load_rmask_d,
            store_wdata: mem_store_wdata_d,
            store_wmask: mem_store_wmask_d,
            alu_csr_result: mem_pipeline.alu_csr_result,
            load_rdata: mem_load_rdata_d,
            pc_wdata: mem_pipeline.pc_wdata,
            valid: mem_pipeline.valid,
            intr: mem_pipeline.intr,
            carried_trap: mem_trap_d
        };
      end
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
    if (id_maindec_trap_valid_comb) begin
      id_trap_d = '{
          valid: 1,
          is_interrupt: 0,
          insn: id_pipeline.insn,
          mcause: id_maindec_mcause_comb,
          pc: id_pipeline.pc,
          next_pc: trap_handler_addr_q,
          rs1_addr: 0,
          rs2_addr: 0,
          rd_addr: 0,
          rs1_rdata: 0,
          rs2_rdata: 0,
          rd_wdata: 0
      };
    end else begin
      id_trap_d = '{default: 0};
    end
  end

  always_comb begin
    ex_trap_d = '{default: 0};

    if (ex_pipeline.carried_trap.valid) begin
      ex_trap_d = ex_pipeline.carried_trap;
    end else if (ex_misaligned_jump_or_branch_comb) begin
      ex_trap_d = '{
          valid: 1,
          is_interrupt: 0,
          insn: ex_pipeline.insn,
          mcause: TRAP_CODE_INSTR_ADDR_MISALIGNED,
          pc: ex_pipeline.pc,
          next_pc: ex_pc_wdata_d,
          rs1_addr: ex_pipeline.rs1_addr,
          rs2_addr: ex_pipeline.rs2_addr,
          rd_addr: ex_pipeline.rd_addr,
          rs1_rdata: ex_rs1_rdata_d,
          rs2_rdata: ex_rs2_rdata_d,
          rd_wdata: 0
      };
    end else begin
      ex_trap_d = '{default: 0};
    end

  end

  always_comb begin
    mem_trap_d = '{default: 0};

    if (mem_pipeline.carried_trap.valid) begin
      mem_trap_d = mem_pipeline.carried_trap;
    end else if (mem_store_trap_valid) begin
      mem_trap_d = '{
          valid: 1,
          is_interrupt: 0,
          insn: mem_pipeline.insn,
          mcause: mem_store_trap_mcause,
          pc: mem_pipeline.pc,
          next_pc: mem_pipeline.pc_wdata,
          rs1_addr: mem_pipeline.rs1_addr,
          rs2_addr: mem_pipeline.rs2_addr,
          rd_addr: mem_pipeline.rd_addr,
          rs1_rdata: mem_pipeline.rs1_rdata,
          rs2_rdata: mem_pipeline.rs2_rdata,
          rd_wdata: 0
      };
    end else if (mem_load_trap_valid) begin
      mem_trap_d = '{
          valid: 1,
          is_interrupt: 0,
          insn: mem_pipeline.insn,
          mcause: mem_load_trap_mcause,
          pc: mem_pipeline.pc,
          next_pc: mem_pipeline.pc_wdata,
          rs1_addr: mem_pipeline.rs1_addr,
          rs2_addr: mem_pipeline.rs2_addr,
          rd_addr: mem_pipeline.rd_addr,
          rs1_rdata: mem_pipeline.rs1_rdata,
          rs2_rdata: mem_pipeline.rs2_rdata,
          rd_wdata: 0
      };
    end else begin
      mem_trap_d = '{default: 0};
    end

  end

  assign wb_trap_d = wb_pipeline.carried_trap.valid ? wb_pipeline.carried_trap : '{default: 0};

  //////////////////////////////////////
  //
  //  HAZARD LOGIC
  //
  //
  ///////////////////////////////////////

  hazard_unit hazard_unit_inst (
      .EX_RS1_ADDR(ex_rs1_addr_d),
      .EX_RS2_ADDR(ex_rs2_addr_d),
      .MEM_RD_ADDR(mem_pipeline.rd_addr),
      .WB_RD_ADDR(wb_rd_addr_masked),
      .EX_RESULT_SEL(ex_pipeline.result_sel),
      .MEM_RESULT_SEL(mem_pipeline.result_sel),
      .WB_RESULT_SEL(wb_pipeline.result_sel),
      .ID_RS1_ADDR(id_rs1_addr_d),
      .ID_RS2_ADDR(id_rs2_addr_d),
      .EX_RD_ADDR(ex_rd_addr_d),
      .EX_IS_PC_REDIRECT(ex_is_pc_redirect),
      .EX_FORWARD_A(ex_forward_a_sel_comb),
      .EX_FORWARD_B(ex_forward_b_sel_comb),
      .ID_FORWARD_A(id_forward_a_comb),
      .ID_FORWARD_B(id_forward_b_comb),
      .IF_ID_FLUSH(if_id_flush),
      .ID_EX_FLUSH(id_ex_flush),
      .EX_MEM_FLUSH(ex_mem_flush),
      .MEM_WB_FLUSH(mem_wb_flush),
      .IF_ID_STALL(if_id_stall),
      .ID_EX_STALL(id_ex_stall),
      .EX_MEM_STALL(ex_mem_stall),
      .MEM_WB_STALL(mem_wb_stall),
      .EX_TRAP_VALID(ex_trap_d.valid),
      .MEM_TRAP_VALID(mem_trap_d.valid),
      .WB_TRAP_VALID(wb_trap_d.valid),
      .WISHBONE_REQ(mem_cmd_req),
      .WISHBONE_DONE(MEM_CMD_DONE_I)
  );


  //////////////////////////////////////
  //
  //  FORMAL VERIFICATION
  //
  //
  ///////////////////////////////////////

`ifdef RISCV_FORMAL


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
  logic rvfi_valid_next;
  assign rvfi_valid_next = mem_wb_stall ? 0 : wb_pipeline.valid;

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
    case (wb_csr_addr_masked)
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

  always_ff @(posedge CLK) begin
    if (RST) begin
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
      rvfi_valid <= rvfi_valid_next;
      if (rvfi_valid_next) rvfi_order <= rvfi_order + 1;
      rvfi_mode <= 3;
      rvfi_ixl  <= 1;
      rvfi_halt <= 0;
      rvfi_trap <= wb_trap_d.valid;
      rvfi_intr <= wb_pipeline.intr;

      if (wb_trap_d.valid) begin
        rvfi_insn <= wb_trap_d.insn;
        rvfi_rs1_addr <= wb_trap_d.rs1_addr;
        rvfi_rs2_addr <= wb_trap_d.rs2_addr;
        rvfi_rs1_rdata <= wb_trap_d.rs1_rdata;
        rvfi_rs2_rdata <= wb_trap_d.rs2_rdata;

        rvfi_rd_addr <= wb_trap_d.rd_addr;
        rvfi_rd_wdata <= wb_trap_d.rd_wdata;

        rvfi_pc_rdata <= wb_trap_d.pc;
        rvfi_pc_wdata <= wb_trap_d.next_pc;

        rvfi_mem_addr <= wb_pipeline.alu_csr_result;
        rvfi_mem_rmask <= wb_pipeline.load_rmask;
        rvfi_mem_wmask <= wb_pipeline.store_wmask;
        rvfi_mem_rdata <= wb_pipeline.load_rdata;
        rvfi_mem_wdata <= wb_pipeline.store_wdata;
      end else begin
        rvfi_insn <= wb_pipeline.insn;
        rvfi_rs1_addr <= wb_pipeline.rs1_addr;
        rvfi_rs2_addr <= wb_pipeline.rs2_addr;
        rvfi_rs1_rdata <= wb_pipeline.rs1_rdata;
        rvfi_rs2_rdata <= wb_pipeline.rs2_rdata;

        rvfi_rd_addr <= wb_rd_addr_masked;
        rvfi_rd_wdata <= wb_rd_wdata_masked;

        rvfi_pc_rdata <= wb_pipeline.pc;
        rvfi_pc_wdata <= wb_trap_d.valid ? trap_handler_addr_q : wb_pipeline.pc_wdata;

        rvfi_mem_addr <= wb_pipeline.alu_csr_result;
        rvfi_mem_rmask <= wb_pipeline.load_rmask;
        rvfi_mem_wmask <= wb_pipeline.store_wmask;
        rvfi_mem_rdata <= wb_pipeline.load_rdata;
        rvfi_mem_wdata <= wb_pipeline.store_wdata;
      end


      // make rmask and wmask cleared if an exception
      rvfi_csr_mcycle_wmask <= is_csr_mcycleh ? {wb_csr_wmask_comb, 32'd0} :
          is_csr_mcycle  ? {32'd0, wb_csr_wmask_comb} :
          64'd0;
      rvfi_csr_minstret_wmask <= is_csr_minstreth ? {wb_csr_wmask_comb, 32'd0} :
          is_csr_minstret  ? {32'd0, wb_csr_wmask_comb} :
          64'd0;
      rvfi_csr_mcause_wmask <= is_csr_mcause ? wb_csr_wmask_comb : 32'd0;
      rvfi_csr_mepc_wmask <= is_csr_mepc ? wb_csr_wmask_comb : 32'd0;
      rvfi_csr_mtvec_wmask <= is_csr_mtvec ? wb_csr_wmask_comb : 32'd0;
      // csr rmask logic
      rvfi_csr_mcycle_rmask <= is_csr_mcycleh ? {wb_csr_rmask_comb, 32'd0} :
          is_csr_mcycle  ? {32'd0, wb_csr_rmask_comb} :
          64'd0;
      rvfi_csr_minstret_rmask <= is_csr_minstreth ?  {wb_csr_rmask_comb, 32'd0} :
          is_csr_minstret  ? {32'd0, wb_csr_rmask_comb} :
          64'd0;
      rvfi_csr_mcause_rmask <= is_csr_mcause ? wb_csr_rmask_comb : 32'd0;
      rvfi_csr_mtvec_rmask <= is_csr_mtvec ? wb_csr_rmask_comb : 32'd0;
      rvfi_csr_mepc_rmask <= is_csr_mepc ? wb_csr_rmask_comb : 32'd0;

      rvfi_csr_mcycle_rdata <= is_csr_mcycleh ? {wb_pipeline.csr_rdata, 32'd0} :
          is_csr_mcycle  ? {32'd0, wb_pipeline.csr_rdata} :
          64'd0;
      rvfi_csr_minstret_rdata <= is_csr_minstreth ? {wb_pipeline.csr_rdata, 32'd0} :
          is_csr_minstret  ? {32'd0, wb_pipeline.csr_rdata} :
          64'd0;
      // csr rdata logic
      rvfi_csr_mcause_rdata <= is_csr_mcause ? wb_pipeline.csr_rdata : 32'd0;
      rvfi_csr_mtvec_rdata <= is_csr_mtvec ? wb_pipeline.csr_rdata : 32'd0;
      rvfi_csr_mepc_rdata <= is_csr_mepc ? wb_pipeline.csr_rdata : 32'd0;

      rvfi_csr_mcycle_wdata <= is_csr_mcycleh ? {wb_pipeline.csr_wdata, 32'd0} :
          is_csr_mcycle  ? {32'd0, wb_pipeline.csr_wdata} :
          64'd0;
      rvfi_csr_minstret_wdata <= is_csr_minstreth ? {wb_pipeline.csr_wdata, 32'd0} :
          is_csr_minstret  ? {32'd0, wb_pipeline.csr_wdata} :
          64'd0;
      rvfi_csr_mcause_wdata <= is_csr_mcause ? wb_pipeline.csr_wdata : 32'd0;
      rvfi_csr_mtvec_wdata <= is_csr_mtvec ? wb_pipeline.csr_wdata : 32'd0;
      rvfi_csr_mepc_wdata <= is_csr_mepc ? wb_pipeline.csr_wdata : 32'd0;

    end
  end
`endif
endmodule
