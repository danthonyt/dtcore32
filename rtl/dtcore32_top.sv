module dtcore32_top (
    input  logic CLK,
    input  logic RST,
    input  logic RX,
    output logic TX

);
  logic rstn;
  assign rstn = ~RST;
  localparam AXIL_ADDR_WIDTH = 32;
  localparam AXIL_BUS_WIDTH = 32;
  localparam IMEM_ADDR_WIDTH = 10;
  localparam DMEM_ADDR_WIDTH = 10;
  logic IMEM_en;
  logic [        IMEM_ADDR_WIDTH-1:0] IMEM_addr;
  logic [        DMEM_ADDR_WIDTH-1:0] DMEM_addr;
  logic [                  31:0] IMEM_rdata;
  logic [                  31:0] DMEM_rdata;
  logic [                  31:0] DMEM_wdata;
  logic [                   3:0] DMEM_wmask;

  // read address channel
  logic [   AXIL_ADDR_WIDTH-1:0] M_AXI_ARADDR;
  logic [                   2:0] M_AXI_ARPROT;
  logic                          M_AXI_ARVALID;
  logic                          M_AXI_ARREADY;
  // read data channel
  logic [    AXIL_BUS_WIDTH-1:0] M_AXI_RDATA;
  logic [                   1:0] M_AXI_RRESP;
  logic                          M_AXI_RVALID;
  logic                          M_AXI_RREADY;
  // write address channel
  logic                          M_AXI_AWVALID;
  logic                          M_AXI_AWREADY;
  logic [   AXIL_ADDR_WIDTH-1:0] M_AXI_AWADDR;
  logic [                   2:0] M_AXI_AWPROT;
  // write data channel
  logic                          M_AXI_WVALID;
  logic                          M_AXI_WREADY;
  logic [    AXIL_BUS_WIDTH-1:0] M_AXI_WDATA;
  logic [(AXIL_BUS_WIDTH/8)-1:0] M_AXI_WSTRB;
  // write response channel
  logic                          M_AXI_BVALID;
  logic                          M_AXI_BREADY;
  logic [                   1:0] M_AXI_BRESP;

  logic                          START_READ;
  logic                          START_WRITE;
  logic                          DONE_READ;
  logic                          DONE_WRITE;
  logic                          BUSY_READ;
  logic                          BUSY_WRITE;

  // peripheral interface
  // put on the axi line
  logic [   AXIL_ADDR_WIDTH-1:0] TRANSACTION_WRADDR;
  logic [    AXIL_BUS_WIDTH-1:0] TRANSACTION_WRDATA;
  logic [   AXIL_ADDR_WIDTH-1:0] TRANSACTION_RADDR;
  logic [(AXIL_BUS_WIDTH/8)-1:0] TRANSACTION_WSTRB;
  // taken from the axi line
  logic [    AXIL_BUS_WIDTH-1:0] TRANSACTION_RDATA;
  logic [31:0] WB_insn;
  logic WB_valid;
  logic dmem_en;


  dtcore32 #(
      .DMEM_ADDR_WIDTH(DMEM_ADDR_WIDTH),
      .IMEM_ADDR_WIDTH(IMEM_ADDR_WIDTH),
      .AXIL_ADDR_WIDTH(AXIL_ADDR_WIDTH),
      .AXIL_BUS_WIDTH (AXIL_BUS_WIDTH)
  ) dtcore32_inst (
      .CLK(CLK),
      .RST(RST),
      .IMEM_RDATA(IMEM_rdata),
      .DMEM_RDATA(DMEM_rdata),
      .IMEM_ADDR(IMEM_addr),
      .DMEM_ADDR(DMEM_addr),
      .DMEM_WDATA(DMEM_wdata),
      .DMEM_WMASK(DMEM_wmask),
      .IMEM_EN(IMEM_en),
      .DMEM_EN(dmem_en),
      .AXIL_START_READ(START_READ),
      .AXIL_START_WRITE(START_WRITE),
      .AXIL_DONE_READ(DONE_READ),
      .AXIL_DONE_WRITE(DONE_WRITE),
      .AXIL_BUSY_READ(BUSY_READ),
      .AXIL_BUSY_WRITE(BUSY_WRITE),
      .AXIL_TRANSACTION_WRADDR(TRANSACTION_WRADDR),
      .AXIL_TRANSACTION_WRDATA(TRANSACTION_WRDATA),
      .AXIL_TRANSACTION_WSTRB(TRANSACTION_WSTRB),
      .AXIL_TRANSACTION_RADDR(TRANSACTION_RADDR),
      .AXIL_TRANSACTION_RDATA(TRANSACTION_RDATA)
  );

  axi_lite_master #(
      .BUS_WIDTH (AXIL_BUS_WIDTH),
      .ADDR_WIDTH(AXIL_ADDR_WIDTH)
  ) axi_lite_master_inst (
      .M_AXI_ACLK(CLK),
      .M_AXI_ARESETN(rstn),
      .M_AXI_ARADDR(M_AXI_ARADDR),
      .M_AXI_ARPROT(M_AXI_ARPROT),
      .M_AXI_ARVALID(M_AXI_ARVALID),
      .M_AXI_ARREADY(M_AXI_ARREADY),
      .M_AXI_RDATA(M_AXI_RDATA),
      .M_AXI_RRESP(M_AXI_RRESP),
      .M_AXI_RVALID(M_AXI_RVALID),
      .M_AXI_RREADY(M_AXI_RREADY),
      .M_AXI_AWVALID(M_AXI_AWVALID),
      .M_AXI_AWREADY(M_AXI_AWREADY),
      .M_AXI_AWADDR(M_AXI_AWADDR),
      .M_AXI_AWPROT(M_AXI_AWPROT),
      .M_AXI_WVALID(M_AXI_WVALID),
      .M_AXI_WREADY(M_AXI_WREADY),
      .M_AXI_WDATA(M_AXI_WDATA),
      .M_AXI_WSTRB(M_AXI_WSTRB),
      .M_AXI_BVALID(M_AXI_BVALID),
      .M_AXI_BREADY(M_AXI_BREADY),
      .M_AXI_BRESP(M_AXI_BRESP),
      .START_READ(START_READ),
      .START_WRITE(START_WRITE),
      .DONE_READ(DONE_READ),
      .DONE_WRITE(DONE_WRITE),
      .BUSY_READ(BUSY_READ),
      .BUSY_WRITE(BUSY_WRITE),
      .TRANSACTION_WRADDR(TRANSACTION_WRADDR),
      .TRANSACTION_WRDATA(TRANSACTION_WRDATA),
      .TRANSACTION_RADDR(TRANSACTION_RADDR),
      .TRANSACTION_WSTRB(TRANSACTION_WSTRB),
      .TRANSACTION_RDATA(TRANSACTION_RDATA),
      .ERROR()
  );

  axi_uartlite_0 your_instance_name (
      .s_axi_aclk   (CLK),            // input wire s_axi_aclk
      .s_axi_aresetn(rstn),           // input wire s_axi_aresetn
      .interrupt    (),               // output wire interrupt
      .s_axi_awaddr (M_AXI_AWADDR[3:0]),   // input wire [3 : 0] s_axi_awaddr
      .s_axi_awvalid(M_AXI_AWVALID),  // input wire s_axi_awvalid
      .s_axi_awready(M_AXI_AWREADY),  // output wire s_axi_awready
      .s_axi_wdata  (M_AXI_WDATA),    // input wire [31 : 0] s_axi_wdata
      .s_axi_wstrb  (M_AXI_WSTRB),    // input wire [3 : 0] s_axi_wstrb
      .s_axi_wvalid (M_AXI_WVALID),   // input wire s_axi_wvalid
      .s_axi_wready (M_AXI_WREADY),   // output wire s_axi_wready
      .s_axi_bresp  (M_AXI_BRESP),    // output wire [1 : 0] s_axi_bresp
      .s_axi_bvalid (M_AXI_BVALID),   // output wire s_axi_bvalid
      .s_axi_bready (M_AXI_BREADY),   // input wire s_axi_bready
      .s_axi_araddr (M_AXI_ARADDR[3:0]),   // input wire [3 : 0] s_axi_araddr
      .s_axi_arvalid(M_AXI_ARVALID),  // input wire s_axi_arvalid
      .s_axi_arready(M_AXI_ARREADY),  // output wire s_axi_arready
      .s_axi_rdata  (M_AXI_RDATA),    // output wire [31 : 0] s_axi_rdata
      .s_axi_rresp  (M_AXI_RRESP),    // output wire [1 : 0] s_axi_rresp
      .s_axi_rvalid (M_AXI_RVALID),   // output wire s_axi_rvalid
      .s_axi_rready (M_AXI_RREADY),   // input wire s_axi_rready
      .rx           (RX),             // input wire rx
      .tx           (TX)              // output wire tx
  );

  dmem #(.ADDR_WIDTH(DMEM_ADDR_WIDTH)) dmem_inst (
      .CLK(CLK),
      .WE(DMEM_wmask),
      .EN(dmem_en),
      .ADDR(DMEM_addr),
      .WDATA(DMEM_wdata),
      .RDATA(DMEM_rdata)
  );

  imem #(.ADDR_WIDTH(IMEM_ADDR_WIDTH)) imem_inst (
      .CLK(CLK),
      .EN(IMEM_en),
      .ADDR(IMEM_addr),
      .RDATA(IMEM_rdata)
  );
endmodule
