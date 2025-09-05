
module dtcore32 (
    input  logic        clk_i,
    input  logic        rst_i,
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
    // to instruction memory interface
    input  logic [31:0] imem_rdata_i,
    output logic [31:0] imem_addr_o,

    // to data memory and peripheral interface
    input logic [31:0] mem_rdata_i,
    input logic mem_done_i,
    output logic mem_valid_o,
    output logic mem_wen_o,
    output logic [31:0] mem_addr_o,
    output logic [31:0] mem_wdata_o,
    output logic [3:0] mem_strb_o

);
  import params_pkg::*;
  localparam RESET_PC = 32'd0;


  logic   if_id_stall;
  logic   if_id_flush;
  if_id_t if_pipeline_d;
  if_id_t id_pipeline_q;
  localparam if_id_t IF_ID_RESET = '{default: 0, insn: NOP_INSTRUCTION};

  logic   id_ex_stall;
  logic   id_ex_flush;
  id_ex_t id_pipeline_d;
  id_ex_t ex_pipeline_q;
  localparam id_ex_t ID_EX_RESET = reset_id_ex();

  logic ex_mem_stall;
  logic ex_mem_flush;
  ex_mem_t ex_pipeline_d;
  ex_mem_t mem_pipeline_q;
  localparam ex_mem_t EX_MEM_RESET = reset_ex_mem();

  logic mem_wb_stall;
  logic mem_wb_flush;
  mem_wb_t mem_pipeline_d;
  mem_wb_t wb_pipeline_q;
  localparam mem_wb_t MEM_WB_RESET = reset_mem_wb();

  logic [31:0] imem_addr;
  logic ex_is_pc_redirect;
  logic [31:0] ex_pc_target;

  logic id_forward_a;
  logic id_forward_b;
  logic [31:0] regfile_rs1_rdata;
  logic [31:0] regfile_rs2_rdata;
  logic [31:0] wb_rd_wdata;

  logic [2:0] ex_forward_a_sel;
  logic [2:0] ex_forward_b_sel;
  logic [31:0] id_csrfile_rdata;

  logic mem_valid;
  logic mem_wen;
  logic [31:0] mem_addr;
  logic [31:0] mem_wdata;
  logic [3:0] mem_strb;

  logic [31:0] wb_csr_rmask;
  logic [31:0] wb_csr_wmask;
  logic [11:0] wb_csr_addr;
  logic [31:0] wb_csr_wdata;
  logic [4:0] wb_rd_addr;
  logic [11:0] id_csrfile_addr;

  logic [31:0] trap_handler_addr_q;

  if_stage #(
      .RESET_PC(RESET_PC)
  ) if_stage_inst (
      .clk_i(clk_i),
      .rst_i(rst_i),
      .if_id_stall_i(if_id_stall),
      .if_id_flush_i(if_id_flush),
      .imem_rdata_i(imem_rdata_i),
      .imem_addr_o(imem_addr),
      .ex_is_pc_redirect_i(ex_is_pc_redirect),
      .ex_pc_target_i(ex_pc_target),
      .wb_trap_valid_i(wb_pipeline_q.trap_valid),
      .trap_handler_addr_i(trap_handler_addr_q),
      .if_pipeline_d(if_pipeline_d)
  );

  pipeline_reg #(
      .pipeline_t(if_id_t),
      .RESET_PIPELINE(IF_ID_RESET)
  ) if_id_reg_inst (
      .clk_i(clk_i),
      .rst_i(rst_i),
      .stall_i(if_id_stall),
      .prev_stage_stall_i(1'b0),
      .flush_i(if_id_flush),
      .pipeline_d(if_pipeline_d),
      .pipeline_q(id_pipeline_q)
  );

  id_stage id_stage_inst (
      .id_forward_a_i(id_forward_a),
      .id_forward_b_i(id_forward_b),
      .regfile_rs1_rdata_i(regfile_rs1_rdata),
      .regfile_rs2_rdata_i(regfile_rs2_rdata),
      .id_csrfile_rdata_i(id_csrfile_rdata),
      .id_csrfile_addr_o(id_csrfile_addr),
      .wb_rd_wdata_i(wb_rd_wdata),
      .id_pipeline_q(id_pipeline_q),
      .id_pipeline_d(id_pipeline_d)
  );

  pipeline_reg #(
      .pipeline_t(id_ex_t),
      .RESET_PIPELINE(ID_EX_RESET)
  ) id_ex_reg_inst (
      .clk_i(clk_i),
      .rst_i(rst_i),
      .stall_i(id_ex_stall),
      .prev_stage_stall_i(if_id_stall),
      .flush_i(id_ex_flush),
      .pipeline_d(id_pipeline_d),
      .pipeline_q(ex_pipeline_q)
  );

  ex_stage ex_stage_inst (
      .ex_forward_a_sel_i(ex_forward_a_sel),
      .ex_forward_b_sel_i(ex_forward_b_sel),
      .mem_alu_csr_result_i(mem_pipeline_q.alu_csr_result),
      .wb_load_rdata_i(wb_pipeline_q.load_rdata),
      .wb_alu_csr_result_i(wb_pipeline_q.alu_csr_result),
      .ex_is_pc_redirect_o(ex_is_pc_redirect),
      .ex_pc_target_o(ex_pc_target),
      .ex_pipeline_q(ex_pipeline_q),
      .ex_pipeline_d(ex_pipeline_d)
  );

  pipeline_reg #(
      .pipeline_t(ex_mem_t),
      .RESET_PIPELINE(EX_MEM_RESET)
  ) ex_mem_reg_inst (
      .clk_i(clk_i),
      .rst_i(rst_i),
      .stall_i(ex_mem_stall),
      .prev_stage_stall_i(id_ex_stall),
      .flush_i(ex_mem_flush),
      .pipeline_d(ex_pipeline_d),
      .pipeline_q(mem_pipeline_q)
  );

  mem_stage mem_stage_inst (
      .clk_i(clk_i),
      .rst_i(rst_i),
      .mem_pipeline_q(mem_pipeline_q),
      .mem_pipeline_d(mem_pipeline_d),
      .mem_rdata_i(mem_rdata_i),
      .mem_done_i(mem_done_i),
      .mem_valid_o(mem_valid),
      .mem_wen_o(mem_wen),
      .mem_addr_o(mem_addr),
      .mem_wdata_o(mem_wdata),
      .mem_strb_o(mem_strb)
  );

  pipeline_reg #(
      .pipeline_t(mem_wb_t),
      .RESET_PIPELINE(MEM_WB_RESET)
  ) mem_wb_reg_inst (
      .clk_i(clk_i),
      .rst_i(rst_i),
      .stall_i(mem_wb_stall),
      .prev_stage_stall_i(ex_mem_stall),
      .flush_i(mem_wb_flush),
      .pipeline_d(mem_pipeline_d),
      .pipeline_q(wb_pipeline_q)
  );

  wb_stage wb_stage_inst (
      .wb_pipeline_q (wb_pipeline_q),
      .wb_csr_addr_o (wb_csr_addr),
      .wb_csr_wdata_o(wb_csr_wdata),
      .wb_rd_addr_o  (wb_rd_addr),
      .wb_rd_wdata_o (wb_rd_wdata)
  );

  // regfile outputs read data to the instruction decode stage 
  // and receives write data from the writeback stage
  regfile regfile_inst (
      .clk_i(clk_i),
      .rst_i(rst_i),
      .rs1_addr_i(id_pipeline_d.rs1_addr),
      .rs2_addr_i(id_pipeline_d.rs2_addr),
      .rd_addr_i(wb_rd_addr),
      .reg_wr_data_i(wb_rd_wdata),
      .rs1_rdata_o(regfile_rs1_rdata),
      .rs2_rdata_o(regfile_rs2_rdata)
  );

  // csrfile outputs read data to the instruction execute stage,
  // with control sent form the instruction decode stage. It
  // receives write data from the write back stage
  csrfile csrfile_inst (
      .clk_i(clk_i),
      .rst_i(rst_i),
      .id_csr_raddr_i(id_csrfile_addr),
      .id_csr_rdata_o(id_csrfile_rdata),
      .wb_rd_addr_i(wb_rd_addr),
      .wb_csr_waddr_i(wb_csr_addr),
      .wb_csr_wdata_i(wb_csr_wdata),
      .wb_csr_rmask_o(wb_csr_rmask),
      .wb_csr_wmask_o(wb_csr_wmask),
      .wb_valid_i(wb_pipeline_q.valid),
      .ex_valid_i(ex_pipeline_d.valid),
      .mem_valid_i(mem_pipeline_d.valid),
      .wb_trap_valid_i(wb_pipeline_q.trap_valid),
      .wb_trap_pc_i(wb_pipeline_q.trap_pc),
      .wb_trap_mcause_i(wb_pipeline_q.trap_mcause),
      .trap_handler_addr_q(trap_handler_addr_q)
  );

  hazard_unit hazard_unit_inst (
      .ex_rs1_addr_i(ex_pipeline_q.rs1_addr),
      .ex_rs2_addr_i(ex_pipeline_q.rs2_addr),
      .mem_rd_addr_i(mem_pipeline_q.rd_addr),
      .wb_rd_addr_i(wb_pipeline_q.rd_addr),
      .ex_result_sel_i(ex_pipeline_q.result_sel),
      .wb_result_sel_i(wb_pipeline_q.result_sel),
      .id_rs1_addr_i(id_pipeline_d.rs1_addr),
      .id_rs2_addr_i(id_pipeline_d.rs2_addr),
      .ex_rd_addr_i(ex_pipeline_q.rd_addr),
      .ex_is_pc_redirect_i(ex_is_pc_redirect),
      .ex_forward_a_sel_o(ex_forward_a_sel),
      .ex_forward_b_sel_o(ex_forward_b_sel),
      .id_forward_a_o(id_forward_a),
      .id_forward_b_o(id_forward_b),
      .if_id_flush_o(if_id_flush),
      .id_ex_flush_o(id_ex_flush),
      .ex_mem_flush_o(ex_mem_flush),
      .mem_wb_flush_o(mem_wb_flush),
      .if_id_stall_o(if_id_stall),
      .id_ex_stall_o(id_ex_stall),
      .ex_mem_stall_o(ex_mem_stall),
      .mem_wb_stall_o(mem_wb_stall),
      .ex_trap_valid_i(ex_pipeline_d.trap_valid),
      .mem_trap_valid_i(mem_pipeline_d.trap_valid),
      .wb_trap_valid_i(wb_pipeline_q.trap_valid),
      .mem_req_i(mem_valid),
      .mem_done_i(mem_done_i)
  );

  assign imem_addr_o = imem_addr;
  assign mem_valid_o = mem_valid;
  assign mem_wen_o   = mem_wen;
  assign mem_addr_o  = mem_addr;
  assign mem_wdata_o = mem_wdata;
  assign mem_strb_o  = mem_strb;

  //////////////////////////////////////
  //
  //  FORMAL VERIFICATION
  //
  //
  ///////////////////////////////////////

`ifdef RISCV_FORMAL
  rvfi_t wb_rvfi;
  logic  is_csr_mstatus;
  logic  is_csr_misa;
  logic  is_csr_mie;
  logic  is_csr_mtvec;
  logic  is_csr_mscratch;
  logic  is_csr_mepc;
  logic  is_csr_mcause;
  logic  is_csr_mtval;
  logic  is_csr_mip;
  logic  is_csr_mcycle;
  logic  is_csr_mcycleh;
  logic  is_csr_minstret;
  logic  is_csr_minstreth;
  logic  is_csr_mvendorid;
  logic  is_csr_marchid;
  logic  is_csr_mimpid;
  logic  is_csr_mhartid;
  logic  is_csr_mconfigptr;
  logic  rvfi_valid_next;
  assign rvfi_valid_next = mem_wb_stall ? 0 : rvfi.valid;

  always_comb begin
    // PC + instruction flow
    wb_rvfi.pc_rdata  = wb_pipeline_q.pc;
    wb_rvfi.pc_wdata  = wb_pipeline_q.next_pc;
    wb_rvfi.insn      = wb_pipeline_q.insn;
    wb_rvfi.valid     = wb_pipeline_q.valid;
    wb_rvfi.intr      = wb_pipeline_q.intr;

    // Register file signals
    wb_rvfi.rs1_addr  = wb_pipeline_q.rs1_addr;
    wb_rvfi.rs2_addr  = wb_pipeline_q.rs2_addr;
    wb_rvfi.rd_addr   = wb_rd_addr;
    wb_rvfi.rs1_rdata = wb_pipeline_q.rs1_rdata;
    wb_rvfi.rs2_rdata = wb_pipeline_q.rs2_rdata;
    wb_rvfi.rd_wdata  = wb_rd_wdata;

    // CSR signals
    wb_rvfi.csr_addr  = wb_csr_addr_masked;
    wb_rvfi.csr_wdata = wb_pipeline_q.csr_wdata;
    wb_rvfi.csr_wmask = wb_csr_wmask;
    wb_rvfi.csr_rdata = wb_pipeline_q.csr_rdata;
    wb_rvfi.csr_rmask = wb_csr_rmask;

    // Memory interface
    wb_rvfi.mem_addr  = wb_pipeline_q.alu_csr_result;
    wb_rvfi.mem_rmask = wb_pipeline_q.load_rmask;
    wb_rvfi.mem_rdata = wb_pipeline_q.load_rdata;
    wb_rvfi.mem_wmask = wb_pipeline_q.store_wmask;
    wb_rvfi.mem_wdata = wb_pipeline_q.store_wdata;

    // Trap info
    wb_rvfi.trap      = wb_pipeline_q.rvfi_trap_info;
  end


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
    case (rvfi.csr_addr)
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
      rvfi_valid <= rvfi_valid_next;
      if (rvfi_valid_next) rvfi_order <= rvfi_order + 1;
      rvfi_mode <= 3;
      rvfi_ixl  <= 1;
      rvfi_halt <= 0;
      rvfi_trap <= rvfi.trap.valid;
      rvfi_intr <= rvfi.intr;

      if (rvfi.trap.valid) begin
        rvfi_insn <= rvfi.trap.insn;
        rvfi_rs1_addr <= rvfi.trap.rs1_addr;
        rvfi_rs2_addr <= rvfi.trap.rs2_addr;
        rvfi_rs1_rdata <= rvfi.trap.rs1_rdata;
        rvfi_rs2_rdata <= rvfi.trap.rs2_rdata;

        rvfi_rd_addr <= rvfi.trap.rd_addr;
        rvfi_rd_wdata <= rvfi.trap.rd_wdata;

        rvfi_pc_rdata <= rvfi.trap.pc;
        rvfi_pc_wdata <= rvfi.trap.next_pc;

        rvfi_mem_addr <= rvfi.mem_addr;
        rvfi_mem_rmask <= rvfi.mem_rmask;
        rvfi_mem_wmask <= rvfi.mem_wmask;
        rvfi_mem_rdata <= rvfi.mem_rdata;
        rvfi_mem_wdata <= rvfi.mem_wdata;
      end else begin
        rvfi_insn <= rvfi.insn;
        rvfi_rs1_addr <= rvfi.rs1_addr;
        rvfi_rs2_addr <= rvfi.rs2_addr;
        rvfi_rs1_rdata <= rvfi.rs1_rdata;
        rvfi_rs2_rdata <= rvfi.rs2_rdata;

        rvfi_rd_addr <= rvfi.rd_addr;
        rvfi_rd_wdata <= rvfi.rd_wdata;

        rvfi_pc_rdata <= rvfi.pc_rdata;
        rvfi_pc_wdata <= rvfi.trap.valid ? trap_handler_addr_q : rvfi.pc_wdata;

        rvfi_mem_addr <= rvfi.mem_addr;
        rvfi_mem_rmask <= rvfi.mem_rmask;
        // shift wmask and wdata if first nonzero bit is not at the lsb
        // riscv formal expects this format
        rvfi_mem_wmask <= rvfi.mem_wmask >> get_shift(rvfi.mem_wmask);
        rvfi_mem_rdata <= rvfi.mem_rdata;
        rvfi_mem_wdata <= rvfi.mem_wdata >> 8 * get_shift(rvfi.mem_wmask);
      end


      // make rmask and wmask cleared if an exception
      rvfi_csr_mcycle_wmask <= is_csr_mcycleh ? {wb_csr_wmask, 32'd0} :
          is_csr_mcycle  ? {32'd0, wb_csr_wmask} :
          64'd0;
      rvfi_csr_minstret_wmask <= is_csr_minstreth ? {wb_csr_wmask, 32'd0} :
          is_csr_minstret  ? {32'd0, wb_csr_wmask} :
          64'd0;
      rvfi_csr_mcause_wmask <= is_csr_mcause ? wb_csr_wmask : 32'd0;
      rvfi_csr_mepc_wmask <= is_csr_mepc ? wb_csr_wmask : 32'd0;
      rvfi_csr_mtvec_wmask <= is_csr_mtvec ? wb_csr_wmask : 32'd0;
      // csr rmask logic
      rvfi_csr_mcycle_rmask <= is_csr_mcycleh ? {wb_csr_rmask, 32'd0} :
          is_csr_mcycle  ? {32'd0, wb_csr_rmask} :
          64'd0;
      rvfi_csr_minstret_rmask <= is_csr_minstreth ?  {wb_csr_rmask, 32'd0} :
          is_csr_minstret  ? {32'd0, wb_csr_rmask} :
          64'd0;
      rvfi_csr_mcause_rmask <= is_csr_mcause ? wb_csr_rmask : 32'd0;
      rvfi_csr_mtvec_rmask <= is_csr_mtvec ? wb_csr_rmask : 32'd0;
      rvfi_csr_mepc_rmask <= is_csr_mepc ? wb_csr_rmask : 32'd0;

      rvfi_csr_mcycle_rdata <= is_csr_mcycleh ? {rvfi.csr_rdata, 32'd0} :
          is_csr_mcycle  ? {32'd0, rvfi.csr_rdata} :
          64'd0;
      rvfi_csr_minstret_rdata <= is_csr_minstreth ? {rvfi.csr_rdata, 32'd0} :
          is_csr_minstret  ? {32'd0, rvfi.csr_rdata} :
          64'd0;
      // csr rdata logic
      rvfi_csr_mcause_rdata <= is_csr_mcause ? rvfi.csr_rdata : 32'd0;
      rvfi_csr_mtvec_rdata <= is_csr_mtvec ? rvfi.csr_rdata : 32'd0;
      rvfi_csr_mepc_rdata <= is_csr_mepc ? rvfi.csr_rdata : 32'd0;

      rvfi_csr_mcycle_wdata <= is_csr_mcycleh ? {rvfi.csr_wdata, 32'd0} :
          is_csr_mcycle  ? {32'd0, rvfi.csr_wdata} :
          64'd0;
      rvfi_csr_minstret_wdata <= is_csr_minstreth ? {rvfi.csr_wdata, 32'd0} :
          is_csr_minstret  ? {32'd0, rvfi.csr_wdata} :
          64'd0;
      rvfi_csr_mcause_wdata <= is_csr_mcause ? rvfi.csr_wdata : 32'd0;
      rvfi_csr_mtvec_wdata <= is_csr_mtvec ? rvfi.csr_wdata : 32'd0;
      rvfi_csr_mepc_wdata <= is_csr_mepc ? rvfi.csr_wdata : 32'd0;

    end
  end

  // Returns the shift amount (LSB index of the mask)
  function integer get_shift;
    input [3:0] wmask;
    integer i;
    logic   found;
    begin
      get_shift = 0;  // default
      found = 0;
      for (i = 0; i < 4; i = i + 1) begin
        if (!found && wmask[i]) begin
          get_shift = i;
          found = 1;
        end
      end
    end
  endfunction

`endif
endmodule
