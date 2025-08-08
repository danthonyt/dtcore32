module rvfi_wrapper (
	input         clock,
	input         reset,
	`RVFI_OUTPUTS
);


(* keep *) `rvformal_rand_reg [31:0] IMEM_rdata_i;
(* keep *) logic [31:0] IMEM_addr_o;
(* keep *) `rvformal_rand_reg [31:0] mem_rdata;
//(* keep *) logic [31:0] mem_rdata;
(* keep *) logic [31:0] mem_addr;
(* keep *) logic [31:0] mem_wdata;

  dtcore32  dtcore32_inst (
    .clk_i(clock),
    .rst_i(reset),
    .IMEM_rdata_i(IMEM_rdata_i),
    .DMEM_rdata_i(mem_rdata),
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
    .IMEM_addr_o(IMEM_addr_o),
    .DMEM_addr_o(mem_addr),
    .DMEM_wdata_o(mem_wdata),
    .DMEM_wmask_o(mem_wmask)
  );


/*
(* keep *) logic [3:0] mem_wmask;
(* keep *) logic [9:0] dmem_short;
(* keep *) logic [9:0] dmem_b0;
(* keep *) logic [9:0] dmem_b1;
(* keep *) logic [9:0] dmem_b2;
(* keep *) logic [9:0] dmem_b3;
assign dmem_short =  mem_addr[9:0];
assign dmem_b0 = dmem_short;
assign dmem_b1 = dmem_short + 1;
assign dmem_b2 = dmem_short + 2;
assign dmem_b3 = dmem_short + 3;
// Example: 4 KB = 4096 bytes
(* keep *) localparam MEM_SIZE = 1024;

(* keep *) logic [7:0] dmem [0:MEM_SIZE-1];  // Byte-addressable
integer i;
always_ff @(posedge clock) begin
  if (reset) begin
  for (i = 0; i < MEM_SIZE; i = i + 1)
        dmem[i] = 8'b0;
  end
end 
always_ff @(posedge clock) begin
  mem_rdata = {dmem[dmem_b3], dmem[dmem_b2], dmem[dmem_b1], dmem[dmem_b0]};
end 
always @(posedge clock) begin
    if (mem_wmask[0])
        dmem[dmem_b0] <= mem_wdata[7:0];
    if (mem_wmask[1])
        dmem[dmem_b1] <= mem_wdata[15:8];
    if (mem_wmask[2])
        dmem[dmem_b2] <= mem_wdata[23:16];
    if (mem_wmask[3])
        dmem[dmem_b3] <= mem_wdata[31:24];    
end
*/

endmodule

