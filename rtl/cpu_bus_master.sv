module cpu_bus_master (
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
    input logic [31:0] cpu_wbm_dat_i,
    input logic cpu_wbm_err_i,
    input logic cpu_wbm_ack_i,
    output logic cpu_wbm_cyc_o,
    output logic cpu_wbm_stb_o,
    output logic [31:0] cpu_wbm_adr_o,
    output logic cpu_wbm_we_o,
    output logic [31:0] cpu_wbm_dat_o,
    output logic [3:0] cpu_wbm_sel_o,

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
      cpu_wbm_cyc_o <= 0;
      cpu_wbm_stb_o <= 0;
      mem_done_o <= 0;
      req_we_q <= 0;
    req_addr_q <= 0;
    req_wdata_q <= 0;
    req_sel_q <= 0;
    mem_rdata_o <= 0;
    end else begin
      case (state)
        IDLE: begin
          dmem_en_o <= 0;
          cpu_wbm_cyc_o <= 0;
          cpu_wbm_stb_o <= 0;
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
              cpu_wbm_cyc_o <= 1;
              cpu_wbm_stb_o <= 1;
            end
          end
        end
        WB_WAIT: begin
          cpu_wbm_stb_o <= 0;
          if (cpu_wbm_ack_i || cpu_wbm_err_i) begin
            state <= IDLE;
            mem_rdata_o <= cpu_wbm_dat_i;
            mem_done_o <= 1;
            cpu_wbm_cyc_o <= 0;
          end
        end
        DMEM_WAIT: begin
          // dmem read is always single cycle
          state <= IDLE;
          mem_rdata_o <= dmem_rdata_i;
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
  assign cpu_wbm_adr_o = req_addr_q;
  assign cpu_wbm_we_o = req_we_q;
  assign cpu_wbm_dat_o = req_wdata_q;
  assign cpu_wbm_sel_o = req_sel_q;

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
