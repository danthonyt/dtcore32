//===========================================================
// Project    : RISC-V SoC
// File       : soc_top.sv
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
    input  logic clk_i,
    input  logic rst_i,
    output  logic led_trap,
    output logic tx_o
);
  localparam MEM_DEPTH = 16384;

  logic [31:0] imem_rdata;
  logic [31:0] imem_addr;
  logic [31:0] mem_rdata;
  logic mem_done;
  logic mem_valid;
  logic mem_wen;
  logic [31:0] mem_addr;
  logic [31:0] mem_wdata;
  logic [3:0] mem_strb;


  logic [31:0] axi_araddr;
  // logic [ 2:0] axi_arprot;
  logic axi_arvalid;
  logic axi_arready;
  logic [31:0] axi_rdata;
  logic [ 1:0] axi_rresp;
  logic axi_rvalid;
  logic axi_rready;
  logic axi_awvalid;
  logic axi_awready;
  logic [31:0] axi_awaddr;
  // logic [ 2:0] axi_awprot;
  logic axi_wvalid;
  logic axi_wready;
  logic [31:0] axi_wdata;
  logic [ 3:0] axi_wstrb;
  logic axi_bvalid;
  logic axi_bready;
  logic [ 1:0] axi_bresp;
  logic [31:0] dmem_rdata;
  logic [31:0] dmem_addr;
  logic dmem_en;
  logic dmem_wen;
  logic [31:0] dmem_wdata;
  logic [3:0] dmem_wstrb;
  logic cpu_err;
  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      led_trap <= 0;
    end else if (cpu_err)begin
      led_trap <= 1;
    end
  end

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
      .mem_strb_o(mem_strb),
      .err_o(cpu_err)
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
    .m_axi_arprot_o(),
    .m_axi_arvalid_o(axi_arvalid),
    .m_axi_arready_i(axi_arready),
    .m_axi_rdata_i(axi_rdata),
    .m_axi_rresp_i(axi_rresp),
    .m_axi_rvalid_i(axi_rvalid),
    .m_axi_rready_o(axi_rready),
    .m_axi_awvalid_o(axi_awvalid),
    .m_axi_awready_i(axi_awready),
    .m_axi_awaddr_o(axi_awaddr),
    .m_axi_awprot_o(),
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
    .dmem_wstrb_o(dmem_wstrb)
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

  rom #(
      .MEM_DEPTH(MEM_DEPTH)
  ) imem_inst (
      .clk_i  (clk_i),
      .addr_i (imem_addr[$clog2(MEM_DEPTH)-1+2:2]),
      .rdata_o(imem_rdata)
  );



endmodule
