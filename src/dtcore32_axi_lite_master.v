module dtcore32_axi_lite_master#(
    parameter BUS_WIDTH = 32
  )(
    // global signals
    input                           m_axi_aclk_i,
    input                           m_axi_aresetn_i,
    // read address channel
    output [31:0]                   m_axi_araddr_o,
    output [3:0]                    m_axi_arcache_o,
    output [2:0]                    m_axi_arprot_o,
    output                          m_axi_arvalid_o,
    input                           m_axi_arready_i,
    // read data channel
    input [BUS_WIDTH-1:0]           m_axi_rdata_i,
    input [1:0]                     m_axi_rresp_i,
    input                           m_axi_rvalid_i,
    output                          m_axi_rready_o,
    // write address channel
    output                          m_axi_awvalid_o,
    input                           m_axi_awready_i,
    output [31:0]                   m_axi_awaddr_o,
    output [2:0]                    m_axi_awprot_o,
    // write data channel
    output                          m_axi_wvalid_o,
    input                           m_axi_wready_i,
    input [BUS_WIDTH-1:0]           m_axi_wdata_i,
    input [(BUS_BYTE_WIDTH/8)-1:0]  m_axi_wstrb_i,
    // write response channel
    input                           m_axi_bvalid_i,
    output                          m_axi_bready_o,
    input [1:0]                     m_axi_bresp_i

  );

  localparam [1:0]  CMD_SUB_RD      = 2'b00,
             CMD_SUB_WR      = 2'b01,
             CMD_SUB_ADDR    = 2'b10,
             CMD_SUB_SPECIAL = 2'b11;
endmodule

