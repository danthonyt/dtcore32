
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
  import params_pkg::*;
  // instruction memory wishbone request is always active
  // unless instruction fetch is stalled 
  assign CPU_FETCH_WBM_CYC_O = !if_id_stall;
  assign CPU_FETCH_WBM_STB_O = !if_id_stall;

  logic if_id_stall;
  logic if_id_flush;
  if_id_t if_pipeline_d;
  if_id_t id_pipeline_q;
  localparam if_id_t IF_ID_RESET = '{default: 0, insn: NOP_INSTRUCTION};

  logic id_ex_stall;
  logic id_ex_flush;
  id_ex_t id_pipeline_d;
  id_ex_t ex_pipeline_q;
  localparam id_ex_t ID_EX_RESET = '{default: 0, insn: NOP_INSTRUCTION};

  logic ex_mem_stall;
  logic ex_mem_flush;
  ex_mem_t ex_pipeline_d;
  ex_mem_t mem_pipeline_q;
  localparam ex_mem_t EX_MEM_RESET = '{default: 0, insn: NOP_INSTRUCTION};

  logic mem_wb_stall;
  logic mem_wb_flush;
  mem_wb_t mem_pipeline_d;
  mem_wb_t wb_pipeline_q;
  localparam mem_wb_t MEM_WB_RESET = '{default: 0, insn: NOP_INSTRUCTION};

  pipeline_reg # (
    .pipeline_t(if_id_t),
    .RESET_PIPELINE(IF_ID_RESET)
  )
  if_id_reg_inst (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .stall_i(if_id_stall),
    .flush_i(if_id_flush),
    .pipeline_d(if_pipeline_d),
    .pipeline_q(id_pipeline_q)
  );

  pipeline_reg # (
    .pipeline_t(id_ex_t),
    .RESET_PIPELINE(ID_EX_RESET)
  )
  id_ex_reg_inst (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .stall_i(id_ex_stall),
    .flush_i(id_ex_flush),
    .pipeline_d(id_pipeline_d),
    .pipeline_q(ex_pipeline_q)
  );

  ex_stage  ex_stage_inst (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .ex_forward_a_sel_i(ex_forward_a_sel_i),
    .ex_forward_b_sel_i(ex_forward_b_sel_i),
    .mem_alu_csr_result_i(mem_alu_csr_result_i),
    .wb_load_rdata_i(wb_load_rdata_i),
    .wb_alu_csr_result_i(wb_alu_csr_result_i),
    .ex_is_pc_redirect_o(ex_is_pc_redirect_o),
    .ex_pc_target_o(ex_pc_target_o),
    .ex_pipeline_q(ex_pipeline_q),
    .ex_pipeline_d(ex_pipeline_d)
  );

  pipeline_reg # (
    .pipeline_t(ex_mem_t),
    .RESET_PIPELINE(EX_MEM_RESET)
  )
  ex_mem_reg_inst (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .stall_i(ex_mem_stall),
    .flush_i(ex_mem_flush),
    .pipeline_d(ex_pipeline_d),
    .pipeline_q(mem_pipeline_q)
  );

  pipeline_reg # (
    .pipeline_t(mem_wb_t),
    .RESET_PIPELINE(MEM_WB_RESET)
  )
  mem_wb_reg_inst (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .stall_i(mem_wb_stall),
    .flush_i(mem_wb_flush),
    .pipeline_d(mem_pipeline_d),
    .pipeline_q(wb_pipeline_q)
  );

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

  regfile regfile_inst (
      .clk_i(clk_i),
      .rst_i(rst_i),
      .rs1_addr_i(id_rs1_addr_d),
      .rs2_addr_i(id_rs2_addr_d),
      .rd_addr_i(wb_rd_addr_masked),
      .reg_wr_data_i(wb_rd_wdata_masked),
      .rs1_rdata_o(id_rs1_rfile_rdata_comb),
      .rs2_rdata_o(id_rs2_rfile_rdata_comb)
  );

  csrfile  csrfile_inst (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .wb_rd_addr_i(wb_rd_addr_i),
    .csr_raddr_i(csr_raddr_i),
    .csr_waddr_i(csr_waddr_i),
    .csr_wdata_i(csr_wdata_i),
    .wb_valid_i(wb_valid_i),
    .wb_trap_i(wb_trap_i),
    .ex_valid_i(ex_valid_i),
    .mem_valid_i(mem_valid_i),
    .wb_valid_i(wb_valid_i),
    .trap_handler_addr_i(trap_handler_addr_i),
    .csr_rdata_q(csr_rdata_q),
    .csr_rmask_o(csr_rmask_o),
    .csr_wmask_o(csr_wmask_o)
  );

  hazard_unit  hazard_unit_inst (
    .ex_rs1_addr_i(ex_pipeline_q.rs1_addr),
    .ex_rs1_addr_i(ex_pipeline_q.rs2_addr),
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
    .ex_trap_valid_i(ex_pipeline_d.carried_trap.valid),
    .mem_trap_valid_i(mem_pipeline_d.carried_trap.valid),
    .wb_trap_valid_i(wb_pipeline_d.carried_trap.valid),
    .wishbone_req_i(wishbone_req),
    .wishbone_done_i(wishbone_done)
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
