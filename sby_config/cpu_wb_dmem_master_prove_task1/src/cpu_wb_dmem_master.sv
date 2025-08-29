// uses the wishbone B4 standard
module cpu_wb_dmem_master #(
    parameter WISHBONE_ADDR_WIDTH = 32,
    parameter WISHBONE_BUS_WIDTH  = 32
) (
    input logic CLK_I,
    input logic RST_I,
    input logic CMD_START_I,
    input logic CMD_WE_I,
    input logic [WISHBONE_ADDR_WIDTH-1:0] CMD_ADDR_I,
    input logic [WISHBONE_BUS_WIDTH-1:0] CMD_WDATA_I,
    input logic [WISHBONE_BUS_WIDTH/8-1:0] CMD_SEL_I,
    output logic [WISHBONE_BUS_WIDTH-1:0] CMD_RDATA_O,
    output logic CMD_BUSY_O,

    input logic [WISHBONE_BUS_WIDTH-1:0] WBM_DAT_I,
    input logic WBM_ERR_I,
    input logic WBM_ACK_I,
    output logic WBM_CYC_O,
    output logic WBM_STB_O,
    output logic [WISHBONE_ADDR_WIDTH-1:0] WBM_ADR_O,
    output logic WBM_WE_O,
    output logic [WISHBONE_BUS_WIDTH-1:0] WBM_DAT_O,
    output logic [WISHBONE_BUS_WIDTH/8-1:0] WBM_SEL_O

);
  logic [WISHBONE_ADDR_WIDTH-1:0] cmd_addr_q;
  logic [WISHBONE_BUS_WIDTH-1:0] cmd_wdata_q;
  logic [WISHBONE_BUS_WIDTH/8-1:0] cmd_sel_q;
  logic cmd_we_q;
  logic cmd_busy;

  always_ff @(posedge CLK_I) begin
    if (RST_I) begin
      WBM_CYC_O  <= 0;
      WBM_STB_O  <= 0;
      cmd_busy <= 0;
      cmd_addr_q <= 0;
      cmd_wdata_q <= 0;
      cmd_sel_q <= 0;
      cmd_we_q <= 0;
    end else begin
          WBM_STB_O  <= 0;
        if (CMD_START_I && !cmd_busy) begin
          WBM_CYC_O  <= 1;
          WBM_STB_O  <= 1;
          cmd_busy <= 1;
          cmd_addr_q <= CMD_ADDR_I;
          cmd_wdata_q <= CMD_WDATA_I;
          cmd_sel_q <= CMD_SEL_I;
          cmd_we_q <= CMD_WE_I;
        end else if (WBM_ACK_I || WBM_ERR_I) begin
          WBM_CYC_O  <= 0;
          WBM_STB_O  <= 0;
          cmd_busy <= 0;
          cmd_addr_q <= 0;
          cmd_wdata_q <= 0;
          cmd_sel_q <= 0;
          cmd_we_q <= 0;
        end 
    end
  end

  assign WBM_WE_O = cmd_we_q;
  assign WBM_SEL_O = cmd_sel_q;
  assign WBM_ADR_O = cmd_addr_q;
  assign WBM_DAT_O = cmd_wdata_q;
  assign CMD_RDATA_O = WBM_DAT_I;
  assign CMD_BUSY_O = cmd_busy;

  /******************************************/
  //
  //    FORMAL VERIFICATION
  //
  /******************************************/
`ifdef FORMAL
  default clocking @(posedge CLK_I);
  endclocking
  initial assume (RST_I);
  assume property (disable iff (RST_I) !WBM_CYC_O |-> ##1 !WBM_ACK_I && !WBM_ERR_I);
  assert property(RST_I |-> ##1 !WBM_CYC_O && !WBM_STB_O);
  assert property(disable iff (RST_I) CMD_START_I && !CMD_BUSY_O |-> ##1 WBM_CYC_O && WBM_STB_O);
  assert property(disable iff (RST_I) WBM_STB_O |-> ##1 !WBM_STB_O);
`endif
endmodule
