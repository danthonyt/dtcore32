module rvfi_wrapper (
    input clock,
    input reset,
    `RVFI_OUTPUTS
);

  localparam WISHBONE_BUS_WIDTH = 32;
  localparam WISHBONE_ADDR_WIDTH = 32;


  (* keep *) logic [WISHBONE_ADDR_WIDTH-1:0] IMEM_CMD_ADDR_O;
  (* keep *) `rvformal_rand_reg [31:0] IMEM_CMD_RDATA_I;
  (* keep *) logic IMEM_RDATA_VALID_I;
  (* keep *) logic MEM_CMD_START_O;
  (* keep *) logic MEM_CMD_WE_O;
  (* keep *) logic [WISHBONE_ADDR_WIDTH-1:0] MEM_CMD_ADDR_O;
  (* keep *) logic [WISHBONE_BUS_WIDTH-1:0] MEM_CMD_WDATA_O;
  (* keep *) logic [(WISHBONE_BUS_WIDTH/8)-1:0] MEM_CMD_SEL_O;
  (* keep *) `rvformal_rand_reg [WISHBONE_BUS_WIDTH-1:0] MEM_CMD_RDATA_I;
  (* keep *) `rvformal_rand_reg MEM_CMD_DONE_I;
  (* keep *) `rvformal_rand_reg MEM_CMD_BUSY_I;
  
  // mem done will eventually rise after start pulse
  assume property (@(posedge clock) MEM_CMD_START_O |-> ##[1:$] MEM_CMD_DONE_I);
  //(* keep *) `rvformal_rand_reg [31:0] rand_rdata;
  /*
  int counter;
  // emulate a wishbone peripheral for the mem stage
  always_ff @(posedge clock)begin
    if (reset) begin
        MEM_CMD_RDATA_I <= 0;
        MEM_CMD_BUSY_I <= 0;
        counter <= 0;
    end else begin 
        counter <= counter + 1;
        if (MEM_CMD_START_O && !MEM_CMD_BUSY_I)begin
        // send data after 3 cycle delay
            MEM_CMD_BUSY_I <= 1;
            counter <= 0;
        end
        if (MEM_CMD_BUSY_I && counter >= 1) begin
            MEM_CMD_BUSY_I <= 0;
            MEM_CMD_RDATA_I <= rand_rdata;
            counter <= 0;
        end

    end
  end
*/
  // emulate a wishbone peripheral for the fetch stage
  always_ff @(posedge clock)begin
    if (reset) begin
        IMEM_RDATA_VALID_I <= 0;
    end else begin 
        IMEM_RDATA_VALID_I <= 1;
    end
  end

  dtcore32 # (
    .WISHBONE_ADDR_WIDTH(WISHBONE_ADDR_WIDTH),
    .WISHBONE_BUS_WIDTH(WISHBONE_BUS_WIDTH)
  )
  dtcore32_inst (
    .CLK(clock),
    .RST(reset),
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
    .IMEM_CMD_ADDR_O(IMEM_CMD_ADDR_O),
    .IMEM_CMD_RDATA_I(IMEM_CMD_RDATA_I),
    .IMEM_RDATA_VALID_I(IMEM_RDATA_VALID_I),
    .MEM_CMD_START_O(MEM_CMD_START_O),
    .MEM_CMD_WE_O(MEM_CMD_WE_O),
    .MEM_CMD_ADDR_O(MEM_CMD_ADDR_O),
    .MEM_CMD_WDATA_O(MEM_CMD_WDATA_O),
    .MEM_CMD_SEL_O(MEM_CMD_SEL_O),
    .MEM_CMD_RDATA_I(MEM_CMD_RDATA_I),
    .MEM_CMD_BUSY_I(MEM_CMD_BUSY_I),
    .MEM_CMD_DONE_I(MEM_CMD_DONE_I)
  );


  /*
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
*/

endmodule

