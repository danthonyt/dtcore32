module rvfi_wrapper (
    input clock,
    input reset,
    `RVFI_OUTPUTS
);

  (* keep *) logic [31:0] imem_addr;
  (* keep *) `rvformal_rand_reg [31:0] imem_rdata;
  (* keep *) logic mem_valid;
  (* keep *) logic mem_wen;
  (* keep *) logic [31:0] mem_addr;
  (* keep *) logic [31:0] mem_wdata;
  (* keep *) logic [3:0] mem_strb;
  (* keep *) `rvformal_rand_reg [31:0] mem_rdata;
  (* keep *) `rvformal_rand_reg mem_done;
  
  // mem done will eventually rise after start pulse
  reg f_past_valid;
  initial f_past_valid = 0;
  always @(posedge clock) begin
    f_past_valid <= 1;
    if (f_past_valid && $past(mem_valid)) begin
      assume(mem_done);
    end
  end

  dtcore32  dtcore32_inst (
    .clk_i(clock),
    .rst_i(reset),
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
    .imem_rdata_i(imem_rdata),
    .imem_addr_o(imem_addr),
    .mem_rdata_i(mem_rdata),
    .mem_done_i(mem_done),
    .mem_valid_o(mem_valid),
    .mem_wen_o(mem_wen),
    .mem_addr_o(mem_addr),
    .mem_wdata_o(mem_wdata),
    .mem_strb_o(mem_strb)
  );

endmodule

