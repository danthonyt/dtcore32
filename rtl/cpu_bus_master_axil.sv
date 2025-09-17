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
    input logic clk_i,
    input logic rst_i,

    // cpu signals
    input logic mem_valid_i,
    input logic mem_wen_i,
    input logic [31:0] mem_addr_i,
    input logic [31:0] mem_wdata_i,
    input logic [3:0] mem_strb_i,
    output logic [31:0] mem_rdata_o,
    output logic mem_done_o,

    // wishbone master signals
    // read address channel
    output logic [31:0] m_axi_araddr_o,
    output logic [ 2:0] m_axi_arprot_o,
    output logic        m_axi_arvalid_o,
    input  logic        m_axi_arready_i,
    // read data channel
    input  logic [31:0] m_axi_rdata_i,
    input  logic [ 1:0] m_axi_rresp_i,
    input  logic        m_axi_rvalid_i,
    output logic        m_axi_rready_o,
    // write address channel
    output logic        m_axi_awvalid_o,
    input  logic        m_axi_awready_i,
    output logic [31:0] m_axi_awaddr_o,
    output logic [ 2:0] m_axi_awprot_o,
    // write data channel
    output logic        m_axi_wvalid_o,
    input  logic        m_axi_wready_i,
    output logic [31:0] m_axi_wdata_o,
    output logic [ 3:0] m_axi_wstrb_o,
    // write response channel
    input  logic        m_axi_bvalid_i,
    output logic        m_axi_bready_o,
    input  logic [ 1:0] m_axi_bresp_i,

    // dmem signals
    input logic [31:0] dmem_rdata_i,
    output logic [31:0] dmem_addr_o,
    output logic dmem_en_o,
    output logic dmem_wen_o,
    output logic [31:0] dmem_wdata_o,
    output logic [3:0] dmem_wstrb_o
);
  logic [31:0] req_addr_q;
  logic [31:0] req_wdata_q;
  logic [3:0] req_sel_q;
  logic req_we_q;
  logic dmem_sel;
  logic uart_sel;

  logic axil_start_read;
  logic axil_start_write;
  logic axil_done_read;
  logic axil_done_write;
  logic [31:0] axil_rdata;

  axi_lite_master #(
      .BUS_WIDTH (32),
      .ADDR_WIDTH(32)
  ) axi_lite_master_inst (
      .m_axi_aclk_i(clk_i),
      .m_axi_aresetn_i(~rst_i),
      .m_axi_araddr_o(m_axi_araddr_o),
      .m_axi_arprot_o(m_axi_arprot_o),
      .m_axi_arvalid_o(m_axi_arvalid_o),
      .m_axi_arready_i(m_axi_arready_i),
      .m_axi_rdata_i(m_axi_rdata_i),
      .m_axi_rresp_i(m_axi_rresp_i),
      .m_axi_rvalid_i(m_axi_rvalid_i),
      .m_axi_rready_o(m_axi_rready_o),
      .m_axi_awvalid_o(m_axi_awvalid_o),
      .m_axi_awready_i(m_axi_awready_i),
      .m_axi_awaddr_o(m_axi_awaddr_o),
      .m_axi_awprot_o(m_axi_awprot_o),
      .m_axi_wvalid_o(m_axi_wvalid_o),
      .m_axi_wready_i(m_axi_wready_i),
      .m_axi_wdata_o(m_axi_wdata_o),
      .m_axi_wstrb_o(m_axi_wstrb_o),
      .m_axi_bvalid_i(m_axi_bvalid_i),
      .m_axi_bready_o(m_axi_bready_o),
      .m_axi_bresp_i(m_axi_bresp_i),
      .start_read_i(axil_start_read),
      .start_write_i(axil_start_write),
      .done_read_o(axil_done_read),
      .done_write_o(axil_done_write),
      .busy_read_o(),
      .busy_write_o(),
      .x_wraddr_i(req_addr_q),
      .x_wrdata_i(req_wdata_q),
      .x_raddr_i(req_addr_q),
      .x_wstrb_i(req_sel_q),
      .x_rdata_o(axil_rdata),
      .err_o()
  );


  assign dmem_sel = mem_addr_i[31:16] == 16'h0010;
  assign uart_sel = mem_addr_i[31:16] == 16'h0100;

  typedef enum {
    IDLE,
    AXIL_WAIT,
    DMEM_WAIT
  } fsm_state;
  fsm_state state;

  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      state <= IDLE;
      dmem_en_o <= 0;
      mem_done_o <= 0;
      req_we_q <= 0;
      req_addr_q <= 0;
      req_wdata_q <= 0;
      req_sel_q <= 0;
      //mem_rdata_o <= 0;
      axil_start_read <= 0;
      axil_start_write <= 0;
    end else begin
      axil_start_read <= 0;
      axil_start_write <= 0;
      case (state)
        IDLE: begin
          dmem_en_o <= 0;
          mem_done_o <= 0;
          if (mem_valid_i) begin
            req_we_q <= mem_wen_i;
            req_addr_q <= mem_addr_i;
            req_wdata_q <= mem_wdata_i;
            req_sel_q <= mem_strb_i;
            if (dmem_sel) begin
              state <= DMEM_WAIT;
              dmem_en_o <= 1;
            end else if (uart_sel) begin
              state <= AXIL_WAIT;
              if (mem_wen_i) axil_start_write <= 1;
              else axil_start_read <= 1;
            end
          end
        end
        AXIL_WAIT: begin        
          if (axil_done_read && !req_we_q) begin
            state <= IDLE;
            //mem_rdata_o <= axil_rdata;
            mem_done_o <= 1;
          end else if (axil_done_write && req_we_q) begin
            state <= IDLE;
            mem_done_o <= 1;
          end
        end
        DMEM_WAIT: begin
          // dmem read is always single cycle
          state <= IDLE;
          //mem_rdata_o <= dmem_rdata_i;
          mem_done_o <= 1;
          dmem_en_o <= 0;
        end
        default: ;
      endcase
    end
  end

  // these signals are only used when the 
  // appropriate peripheral is active
  assign dmem_addr_o = req_addr_q;
  assign dmem_wen_o = req_we_q;
  assign dmem_wdata_o = req_wdata_q;
  assign dmem_wstrb_o = req_sel_q;
  // modify fsm so mem rdata is asynchronous
  assign mem_rdata_o = axil_done_read ? axil_rdata : dmem_rdata_i;
endmodule
