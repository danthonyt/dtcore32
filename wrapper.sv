module rvfi_wrapper (
	input         clock,
	input         reset,
	`RVFI_OUTPUTS
);

localparam BUS_WIDTH = 32;
localparam ADDR_WIDTH = 32;
localparam DMEM_ADDR_WIDTH = 10;
localparam IMEM_ADDR_WIDTH = 10;
(* keep *) `rvformal_rand_reg [31:0] imem_rdata;
(* keep *) logic [IMEM_ADDR_WIDTH-1:0] imem_addr;
//(* keep *) `rvformal_rand_reg [31:0] dmem_rdata;
(* keep *) logic [31:0] dmem_rdata;
(* keep *) logic [DMEM_ADDR_WIDTH-1:0] dmem_addr;
(* keep *) logic [31:0] dmem_wdata;
(* keep *) logic [3:0] dmem_wmask;
(* keep *) logic dmem_en;
(* keep *) logic imem_en;

  dtcore32 # (
    .DMEM_ADDR_WIDTH(DMEM_ADDR_WIDTH),
    .IMEM_ADDR_WIDTH(IMEM_ADDR_WIDTH)
  )
  dtcore32_inst (
    .CLK(clock),
    .RST(reset),
    .IMEM_RDATA(imem_rdata),
    .DMEM_RDATA(dmem_rdata),
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
    .IMEM_ADDR(imem_addr),
    .DMEM_ADDR(dmem_addr),
    .DMEM_WDATA(dmem_wdata),
    .DMEM_WMASK(dmem_wmask),
    .DMEM_EN(dmem_en),
    .IMEM_EN(imem_en),
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
    .WE(dmem_wmask),
    .EN(dmem_en),
    .ADDR(dmem_addr),
    .WDATA(dmem_wdata),
    .RDATA(dmem_rdata)
  );


// MMIO address range
localparam MMIO_BASE = 32'h2400;
localparam MMIO_END  = 32'h2410;
localparam DMEM_BASE = 32'h1000;
localparam DMEM_END  = 32'h1400;
sequence MMIO_MEM_INSTR;
(rvfi_mem_addr < MMIO_END) && (rvfi_mem_addr >= MMIO_BASE) ||  (rvfi_mem_rmask == 0 || rvfi_mem_wmask == 0);
endsequence
sequence DMEM_MEM_INSTR;
(rvfi_insn[6:0] != 7'b0000011 && rvfi_insn[6:0] != 7'b0100011) // not LW/SW 801fa103
    || ((rvfi_mem_addr >= DMEM_BASE && rvfi_mem_addr < DMEM_END));
endsequence

assume property(@(posedge clock) disable iff (reset) DMEM_MEM_INSTR);

assume property (@(posedge clock)
    // if memory access is inside MMIO region
    ((rvfi_mem_addr >= MMIO_BASE) && (rvfi_mem_addr < MMIO_END)) |-> 
        // instruction must be LW or SW
        (((rvfi_insn[6:0] == 7'b0000011 && rvfi_insn[14:12] == 3'b010) || // LW
         (rvfi_insn[6:0] == 7'b0100011 && rvfi_insn[14:12] == 3'b010)) && // SW
         (rvfi_mem_addr[1:0] == 2'b00 ))  
);

endmodule

