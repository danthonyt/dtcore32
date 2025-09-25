//===========================================================
// Project    : RISC-V SoC
// File       : soc_top.v
// Module     : soc_top
// Description: Top-level system-on-chip (SoC) module. Integrates
//              the RISC-V CPU core, memory modules, peripherals,
//              and I/O interfaces (e.g., UART) into a single design.
//
// Inputs:
//   clk_i   - System clock
//   rst_i   - Synchronous reset
//   rx_i    - UART receive line
//
// Outputs:
//   tx_o    - UART transmit line
//
// Notes:
//   - Instantiates CPU core (`dtcore32`), memories (`ram`, `rom`),
//     pipeline control units, and peripherals.
//   - Provides a single top-level interface for clock, reset, and UART I/O.
//   - Designed to be the entry point for synthesis and simulation of the SoC.
//
// Author     : David Torres
// Date       : 2025-09-16
//===========================================================

module soc_top (
    input   clk_i,
    input   rst_i,
    output  tx_o
);
  localparam MEM_DEPTH = 16384;

  wire [31:0] imem_rdata;
  wire [31:0] imem_addr;
  wire [31:0] mem_rdata;
  wire mem_done;
  wire mem_valid;
  wire mem_wen;
  wire [31:0] mem_addr;
  wire [31:0] mem_wdata;
  wire [3:0] mem_strb;


  wire [31:0] axi_araddr;
  // wire [ 2:0] axi_arprot;
  wire axi_arvalid;
  wire axi_arready;
  wire [31:0] axi_rdata;
  wire [ 1:0] axi_rresp;
  wire axi_rvalid;
  wire axi_rready;
  wire axi_awvalid;
  wire axi_awready;
  wire [31:0] axi_awaddr;
  // wire [ 2:0] axi_awprot;
  wire axi_wvalid;
  wire axi_wready;
  wire [31:0] axi_wdata;
  wire [ 3:0] axi_wstrb;
  wire axi_bvalid;
  wire axi_bready;
  wire [ 1:0] axi_bresp;
  wire [31:0] dmem_rdata;
  wire [31:0] dmem_addr;
  wire dmem_en;
  wire dmem_wen;
  wire [31:0] dmem_wdata;
  wire [3:0] dmem_wstrb;

  wire [31:0] rom_addr;
  wire [31:0] rom_rdata;
  wire rom_en;

  dtcore32 dtcore32_inst (
      .clk_i(clk_i),
      .rst_i(rst_i),
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

  cpu_bus_master_axil  cpu_bus_master_axil_inst (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .mem_valid_i(mem_valid),
    .mem_wen_i(mem_wen),
    .mem_addr_i(mem_addr),
    .mem_wdata_i(mem_wdata),
    .mem_strb_i(mem_strb),
    .mem_rdata_o(mem_rdata),
    .mem_done_o(mem_done),
    .m_axi_araddr_o(axi_araddr),
    .m_axi_arvalid_o(axi_arvalid),
    .m_axi_arready_i(axi_arready),
    .m_axi_rdata_i(axi_rdata),
    .m_axi_rresp_i(axi_rresp),
    .m_axi_rvalid_i(axi_rvalid),
    .m_axi_rready_o(axi_rready),
    .m_axi_awvalid_o(axi_awvalid),
    .m_axi_awready_i(axi_awready),
    .m_axi_awaddr_o(axi_awaddr),
    .m_axi_wvalid_o(axi_wvalid),
    .m_axi_wready_i(axi_wready),
    .m_axi_wdata_o(axi_wdata),
    .m_axi_wstrb_o(axi_wstrb),
    .m_axi_bvalid_i(axi_bvalid),
    .m_axi_bready_o(axi_bready),
    .m_axi_bresp_i(axi_bresp),
    .dmem_rdata_i(dmem_rdata),
    .dmem_addr_o(dmem_addr),
    .dmem_en_o(dmem_en),
    .dmem_wen_o(dmem_wen),
    .dmem_wdata_o(dmem_wdata),
    .dmem_wstrb_o(dmem_wstrb),
    .rom_rdata_i(rom_rdata),
    .rom_addr_o(rom_addr),
    .rom_en_o(rom_en)
  );

  axi_uartlite_0 uart_inst (
  .s_axi_aclk(clk_i),        // input wire s_axi_aclk
  .s_axi_aresetn(~rst_i),  // input wire s_axi_aresetn
  .interrupt(),          // output wire interrupt
  .s_axi_awaddr(axi_awaddr[3:0]),    // input wire [3 : 0] s_axi_awaddr
  .s_axi_awvalid(axi_awvalid),  // input wire s_axi_awvalid
  .s_axi_awready(axi_awready),  // output wire s_axi_awready
  .s_axi_wdata(axi_wdata),      // input wire [31 : 0] s_axi_wdata
  .s_axi_wstrb(axi_wstrb),      // input wire [3 : 0] s_axi_wstrb
  .s_axi_wvalid(axi_wvalid),    // input wire s_axi_wvalid
  .s_axi_wready(axi_wready),    // output wire s_axi_wready
  .s_axi_bresp(axi_bresp),      // output wire [1 : 0] s_axi_bresp
  .s_axi_bvalid(axi_bvalid),    // output wire s_axi_bvalid
  .s_axi_bready(axi_bready),    // input wire s_axi_bready
  .s_axi_araddr(axi_araddr[3:0]),    // input wire [3 : 0] s_axi_araddr
  .s_axi_arvalid(axi_arvalid),  // input wire s_axi_arvalid
  .s_axi_arready(axi_arready),  // output wire s_axi_arready
  .s_axi_rdata(axi_rdata),      // output wire [31 : 0] s_axi_rdata
  .s_axi_rresp(axi_rresp),      // output wire [1 : 0] s_axi_rresp
  .s_axi_rvalid(axi_rvalid),    // output wire s_axi_rvalid
  .s_axi_rready(axi_rready),    // input wire s_axi_rready
  .rx(1'b1),                        // input wire rx
  .tx(tx_o)                        // output wire tx
);

  ram #(
      .MEM_DEPTH(MEM_DEPTH)
  ) dmem_inst (
      .clk_i(clk_i),
      .addr_i(dmem_addr[$clog2(MEM_DEPTH)-1+2:2]),
      .en_i(dmem_en),
      .wen_i(dmem_wen),
      .wdata_i(dmem_wdata),
      .wstrb_i(dmem_wstrb),
      .rdata_o(dmem_rdata)
  );

  rom # (
    .MEM_DEPTH(MEM_DEPTH)
  )
  rom_inst (
    .clk_i(clk_i),
    .insn_addr_i(imem_addr[$clog2(MEM_DEPTH)-1+2:2]),
    .mem_addr_i(rom_addr[$clog2(MEM_DEPTH)-1+2:2]),
    .mem_en_i(rom_en),
    .insn_rdata_o(imem_rdata),
    .mem_rdata_o(rom_rdata)
  );

endmodule
