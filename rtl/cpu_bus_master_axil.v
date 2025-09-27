//===========================================================
// Project    : RISC-V CPU
// File       : cpu_bus_master_axil.sv
// Module     : cpu_bus_master_axil
// Description: AXI-lite bus master interface for CPU memory operations.
//              Translates CPU memory requests to AXI-lite transactions
//              for both instruction and data accesses.
//
// Inputs:
//   clk_i          - System clock
//   rst_i          - Synchronous reset
//   mem_valid_i    - High when CPU requests a memory transaction
//   mem_wen_i      - High for write, low for read
//   mem_addr_i     - CPU memory address
//   mem_wdata_i    - CPU write data
//   mem_strb_i     - Byte-enable for write operations
//   m_axi_arready_i - AXI read address ready
//   m_axi_rdata_i  - AXI read data
//   m_axi_rresp_i  - AXI read response
//   m_axi_rvalid_i - AXI read valid
//   m_axi_awready_i- AXI write address ready
//   m_axi_wready_i - AXI write data ready
//   m_axi_bvalid_i - AXI write response valid
//   m_axi_bresp_i  - AXI write response
//   dmem_rdata_i   - Data read from CPU data memory
//
// Outputs:
//   mem_rdata_o    - Data read from memory back to CPU
//   mem_done_o     - High when CPU memory transaction is complete
//   m_axi_araddr_o - AXI read address
//   m_axi_arprot_o - AXI read protection type
//   m_axi_arvalid_o- AXI read address valid
//   m_axi_rready_o - AXI read ready
//   m_axi_awvalid_o- AXI write address valid
//   m_axi_awaddr_o - AXI write address
//   m_axi_awprot_o - AXI write protection type
//   m_axi_wvalid_o - AXI write data valid
//   m_axi_wdata_o  - AXI write data
//   m_axi_wstrb_o  - AXI write byte strobe
//   m_axi_bready_o - AXI write response ready
//   dmem_addr_o    - CPU data memory address
//   dmem_en_o      - Data memory enable
//   dmem_wen_o     - Data memory write enable
//   dmem_wdata_o   - Data memory write data
//   dmem_wstrb_o   - Data memory write strobe
//
// Notes:
//   - Supports AXI-lite single-beat read/write transactions.
//   - Handles CPU memory requests and translates them to AXI signals.
//   - Designed for integration with RISC-V CPU pipeline.
//
// Author     : David Torres
// Date       : 2025-09-16
//===========================================================

module cpu_bus_master_axil (
  input              clk_i          ,
  input              rst_i          ,
  // cpu signals
  input              mem_valid_i    ,
  input              mem_wen_i      ,
  input       [31:0] mem_addr_i     ,
  input       [31:0] mem_wdata_i    ,
  input       [ 3:0] mem_strb_i     ,
  output reg  [31:0] mem_rdata_o    ,
  output reg         mem_done_o     ,
  // wishbone master signals
  // read address channel
  output      [31:0] m_axi_araddr_o ,
  output             m_axi_arvalid_o,
  input              m_axi_arready_i,
  // read data channel
  input       [31:0] m_axi_rdata_i  ,
  input       [ 1:0] m_axi_rresp_i  ,
  input              m_axi_rvalid_i ,
  output             m_axi_rready_o ,
  // write address channel
  output             m_axi_awvalid_o,
  input              m_axi_awready_i,
  output      [31:0] m_axi_awaddr_o ,
  // write data channel
  output             m_axi_wvalid_o ,
  input              m_axi_wready_i ,
  output      [31:0] m_axi_wdata_o  ,
  output      [ 3:0] m_axi_wstrb_o  ,
  // write response channel
  input              m_axi_bvalid_i ,
  output             m_axi_bready_o ,
  input       [ 1:0] m_axi_bresp_i  ,
  // dmem signals
  input       [31:0] dmem_rdata_i   ,
  output wire [31:0] dmem_addr_o    ,
  output reg         dmem_en_o      ,
  output wire        dmem_wen_o     ,
  output wire [31:0] dmem_wdata_o   ,
  output wire [ 3:0] dmem_wstrb_o   ,
  // read only memory signals
  input       [31:0] rom_rdata_i    ,
  output wire [31:0] rom_addr_o     ,
  output reg         rom_en_o
);
  reg  [31:0] req_addr_q ;
  reg  [31:0] req_wdata_q;
  reg  [ 3:0] req_sel_q  ;
  reg         req_we_q   ;
  wire        dmem_sel   ;
  wire        uart_sel   ;
  wire        rom_sel    ;

  reg         axil_start_read ;
  reg         axil_start_write;
  wire        axil_done_read  ;
  wire        axil_done_write ;
  wire [31:0] axil_rdata      ;

  // wishbone master signals
  // read address channel
  wire [31:0] m_axi_araddr ;
  wire        m_axi_arvalid;
  // read data channel
  wire m_axi_rready;
  // write address channel
  wire        m_axi_awvalid;
  wire [31:0] m_axi_awaddr ;
  // write data channel
  wire        m_axi_wvalid;
  wire [31:0] m_axi_wdata ;
  wire [ 3:0] m_axi_wstrb ;
  // write response channel
  wire m_axi_bready;
// Read address channel
  assign m_axi_araddr_o  = m_axi_araddr;
  assign m_axi_arvalid_o = m_axi_arvalid;

// Read data channel
  assign m_axi_rready_o = m_axi_rready;

// Write address channel
  assign m_axi_awvalid_o = m_axi_awvalid;
  assign m_axi_awaddr_o  = m_axi_awaddr;

// Write data channel
  assign m_axi_wvalid_o = m_axi_wvalid;
  assign m_axi_wdata_o  = m_axi_wdata;
  assign m_axi_wstrb_o  = m_axi_wstrb;

// Write response channel
  assign m_axi_bready_o = m_axi_bready;




  axi_lite_master #(
    .BUS_WIDTH (32),
    .ADDR_WIDTH(32)
  ) axi_lite_master_inst (
    .m_axi_aclk_i   (clk_i           ),
    .m_axi_aresetn_i(~rst_i          ),
    .m_axi_araddr_o (m_axi_araddr    ),
    .m_axi_arvalid_o(m_axi_arvalid   ),
    .m_axi_arready_i(m_axi_arready_i ),
    .m_axi_rdata_i  (m_axi_rdata_i   ),
    .m_axi_rresp_i  (m_axi_rresp_i   ),
    .m_axi_rvalid_i (m_axi_rvalid_i  ),
    .m_axi_rready_o (m_axi_rready    ),
    .m_axi_awvalid_o(m_axi_awvalid   ),
    .m_axi_awready_i(m_axi_awready_i ),
    .m_axi_awaddr_o (m_axi_awaddr    ),
    .m_axi_wvalid_o (m_axi_wvalid    ),
    .m_axi_wready_i (m_axi_wready_i  ),
    .m_axi_wdata_o  (m_axi_wdata     ),
    .m_axi_wstrb_o  (m_axi_wstrb     ),
    .m_axi_bvalid_i (m_axi_bvalid_i  ),
    .m_axi_bready_o (m_axi_bready    ),
    .m_axi_bresp_i  (m_axi_bresp_i   ),
    .start_read_i   (axil_start_read ),
    .start_write_i  (axil_start_write),
    .done_read_o    (axil_done_read  ),
    .done_write_o   (axil_done_write ),
    .busy_read_o    (                ),
    .busy_write_o   (                ),
    .x_wraddr_i     (req_addr_q      ),
    .x_wrdata_i     (req_wdata_q     ),
    .x_raddr_i      (req_addr_q      ),
    .x_wstrb_i      (req_sel_q       ),
    .x_rdata_o      (axil_rdata      )
  );


  assign dmem_sel = mem_addr_i[31:16] == 16'h0010;
  assign uart_sel = mem_addr_i[31:16] == 16'h0100;
  assign rom_sel  = mem_addr_i[31:16] == 16'h0000;

  localparam [2:0] IDLE = 3'd0,
    AXIL_WAIT = 3'd1,
    DMEM_WAIT1 = 3'd2,
    DMEM_WAIT2 = 3'd3,
    ROM_WAIT1 = 3'd4,
    ROM_WAIT2 = 3'd5;
  reg [2:0] state;
  always @(posedge clk_i) begin
    if (rst_i) begin
      state            <= IDLE;
      dmem_en_o        <= 0;
      mem_done_o       <= 0;
      req_we_q         <= 0;
      req_addr_q       <= 0;
      req_wdata_q      <= 0;
      req_sel_q        <= 0;
      //mem_rdata_o <= 0;
      axil_start_read  <= 0;
      axil_start_write <= 0;
    end else begin
      axil_start_read  <= 0;
      axil_start_write <= 0;
      case (state)
        IDLE : begin
          dmem_en_o  <= 0;
          mem_done_o <= 0;
          if (mem_valid_i) begin
            req_we_q    <= mem_wen_i;
            req_addr_q  <= mem_addr_i;
            req_wdata_q <= mem_wdata_i;
            req_sel_q   <= mem_strb_i;
            if (dmem_sel) begin
              state     <= DMEM_WAIT1;
              dmem_en_o <= 1;
            end else if (uart_sel) begin
              state <= AXIL_WAIT;
              if (mem_wen_i) axil_start_write <= 1;
              else axil_start_read <= 1;
            end else if (rom_sel) begin
              state    <= ROM_WAIT1;
              rom_en_o <= 1;
            end
          end
        end
        AXIL_WAIT : begin
          if (axil_done_read && !req_we_q) begin
            state       <= IDLE;
            mem_rdata_o <= axil_rdata;
            mem_done_o  <= 1;
          end else if (axil_done_write && req_we_q) begin
            state      <= IDLE;
            mem_done_o <= 1;
          end
        end
        DMEM_WAIT1 : begin
          state <= DMEM_WAIT2;
        end
        DMEM_WAIT2 : begin
          state       <= IDLE;
          mem_rdata_o <= dmem_rdata_i;
          mem_done_o  <= 1;
          dmem_en_o   <= 0;
        end
        ROM_WAIT1 : begin
          state <= ROM_WAIT2;
        end
        ROM_WAIT2 : begin
          state       <= IDLE;
          mem_rdata_o <= rom_rdata_i;
          mem_done_o  <= 1;
          rom_en_o    <= 0;
        end

        default : ;
      endcase
    end
  end

  // these signals are only used when the
  // appropriate peripheral is active
  assign dmem_addr_o  = req_addr_q;
  assign dmem_wen_o   = req_we_q;
  assign dmem_wdata_o = req_wdata_q;
  assign dmem_wstrb_o = req_sel_q;
  assign rom_addr_o   = req_addr_q;
endmodule
