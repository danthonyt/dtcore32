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
    WB_WAIT,
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
              state <= WB_WAIT;
              if (mem_wen_i) axil_start_write <= 1;
              else axil_start_read <= 1;
            end
          end
        end
        WB_WAIT: begin        
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

  /******************************************/
  //
  //    FORMAL VERIFICATION
  //
  /******************************************/
`ifdef FORMAL
  default clocking @(posedge CLK_I);
  endclocking
  initial assume (RST_I);
  assume property (disable iff (RST_I) !CPU_MEM_WBM_CYC_O |-> ##1 !CPU_MEM_WBM_ACK_I && !CPU_MEM_WBM_ERR_I);
  assert property (RST_I |-> ##1 !CPU_MEM_WBM_CYC_O && !CPU_MEM_WBM_STB_O);
  assert property(disable iff (RST_I) CPU_MEM_CMD_START_I && !CPU_MEM_CMD_BUSY_O |-> ##1 CPU_MEM_WBM_CYC_O && CPU_MEM_WBM_STB_O);
  assert property (disable iff (RST_I) CPU_MEM_WBM_STB_O |-> ##1 !CPU_MEM_WBM_STB_O);
`endif
endmodule
