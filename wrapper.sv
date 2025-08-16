module rvfi_wrapper (
	input         clock,
	input         reset,
	`RVFI_OUTPUTS
);

localparam BUS_WIDTH = 32;
localparam ADDR_WIDTH = 32;
localparam DMEM_ADDR_WIDTH = 10;
localparam IMEM_ADDR_WIDTH = 10;
(* keep *) `rvformal_rand_reg [31:0] IMEM_rdata;
(* keep *) logic [IMEM_ADDR_WIDTH-1:0] IMEM_addr;
//(* keep *) `rvformal_rand_reg [31:0] DMEM_rdata;
(* keep *) logic [31:0] DMEM_rdata;
(* keep *) logic [DMEM_ADDR_WIDTH-1:0] DMEM_addr;
(* keep *) logic [31:0] DMEM_wdata;
(* keep *) logic [3:0] DMEM_wmask;
(* keep *) logic DMEM_en;

  dtcore32 # (
    .DMEM_ADDR_WIDTH(DMEM_ADDR_WIDTH),
    .IMEM_ADDR_WIDTH(IMEM_ADDR_WIDTH)
  )
  dtcore32_inst (
    .CLK(clock),
    .RST(reset),
    .IMEM_RDATA(IMEM_rdata),
    .DMEM_RDATA(DMEM_rdata),
    .rvfi_valid(rvfi_valid),
    .rvfi_order(rvfi_order),
    .rvfi_insn(rvfi_insn),
    .rvfi_trap(rvfi_trap),
    .rvfi_halt(rvfi_halt),
    .rvfi_intr(rvfi_intr),
    .rvfi_mode(rvfi_mode),
    .rvfi_ixl(rvfi_ixl),
    .rvfi_rs1_addr(rvfi_rs1_addr),
    .rvfi_rs2_addr(rvfi_rs2_addr),
    .rvfi_rs1_rdata(rvfi_rs1_rdata),
    .rvfi_rs2_rdata(rvfi_rs2_rdata),
    .rvfi_rd_addr(rvfi_rd_addr),
    .rvfi_rd_wdata(rvfi_rd_wdata),
    .rvfi_pc_rdata(rvfi_pc_rdata),
    .rvfi_pc_wdata(rvfi_pc_wdata),
    .rvfi_mem_addr(rvfi_mem_addr),
    .rvfi_mem_rmask(rvfi_mem_rmask),
    .rvfi_mem_wmask(rvfi_mem_wmask),
    .rvfi_mem_rdata(rvfi_mem_rdata),
    .rvfi_mem_wdata(rvfi_mem_wdata),
    .rvfi_csr_mcycle_rmask(rvfi_csr_mcycle_rmask),
    .rvfi_csr_mcycle_wmask(rvfi_csr_mcycle_wmask),
    .rvfi_csr_mcycle_rdata(rvfi_csr_mcycle_rdata),
    .rvfi_csr_mcycle_wdata(rvfi_csr_mcycle_wdata),
    .rvfi_csr_minstret_rmask(rvfi_csr_minstret_rmask),
    .rvfi_csr_minstret_wmask(rvfi_csr_minstret_wmask),
    .rvfi_csr_minstret_rdata(rvfi_csr_minstret_rdata),
    .rvfi_csr_minstret_wdata(rvfi_csr_minstret_wdata),
    .rvfi_csr_mcause_rmask(rvfi_csr_mcause_rmask),
    .rvfi_csr_mcause_wmask(rvfi_csr_mcause_wmask),
    .rvfi_csr_mcause_rdata(rvfi_csr_mcause_rdata),
    .rvfi_csr_mcause_wdata(rvfi_csr_mcause_wdata),
    .rvfi_csr_mepc_rmask(rvfi_csr_mepc_rmask),
    .rvfi_csr_mepc_wmask(rvfi_csr_mepc_wmask),
    .rvfi_csr_mepc_rdata(rvfi_csr_mepc_rdata),
    .rvfi_csr_mepc_wdata(rvfi_csr_mepc_wdata),
    .rvfi_csr_mtvec_rmask(rvfi_csr_mtvec_rmask),
    .rvfi_csr_mtvec_wmask(rvfi_csr_mtvec_wmask),
    .rvfi_csr_mtvec_rdata(rvfi_csr_mtvec_rdata),
    .rvfi_csr_mtvec_wdata(rvfi_csr_mtvec_wdata),
    .IMEM_ADDR(IMEM_addr),
    .DMEM_ADDR(DMEM_addr),
    .DMEM_WDATA(DMEM_wdata),
    .DMEM_WMASK(DMEM_wmask),
    .DMEM_EN(DMEM_en),
    .AXIL_START_READ(),
    .AXIL_START_WRITE(),
    .AXIL_DONE_READ(1'b0),
    .AXIL_DONE_WRITE(1'b0),
    .AXIL_BUSY_READ(1'b0),
    .AXIL_BUSY_WRITE(1'b0),
    .AXIL_TRANSACTION_WRADDR(),
    .AXIL_TRANSACTION_WRDATA(),
    .AXIL_TRANSACTION_WSTRB(),
    .AXIL_TRANSACTION_RADDR(),
    .AXIL_TRANSACTION_RDATA(32'd0)
  );



  dmem  #(.ADDR_WIDTH(DMEM_ADDR_WIDTH)) dmem_inst (
    .CLK(clock),
    .WE(DMEM_wmask),
    .EN(DMEM_en),
    .ADDR(DMEM_addr),
    .WDATA(DMEM_wdata),
    .RDATA(DMEM_rdata)
  );

// only test dmem, not axil interface
assume property(@(posedge clock) rvfi_mem_addr <= 32'h3ff);
endmodule

