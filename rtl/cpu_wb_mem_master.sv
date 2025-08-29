// uses the wishbone B4 standard
module cpu_wb_mem_master #(
    parameter WISHBONE_ADDR_WIDTH = 32,
    parameter WISHBONE_BUS_WIDTH  = 32
) (
    input logic CLK_I,
    input logic RST_I,
    input logic CPU_MEM_CMD_START_I,
    input logic CPU_MEM_CMD_WE_I,
    input logic [WISHBONE_ADDR_WIDTH-1:0] CPU_MEM_CMD_ADDR_I,
    input logic [WISHBONE_BUS_WIDTH-1:0] CPU_MEM_CMD_WDATA_I,
    input logic [WISHBONE_BUS_WIDTH/8-1:0] CPU_MEM_CMD_SEL_I,
    output logic [WISHBONE_BUS_WIDTH-1:0] CPU_MEM_CMD_RDATA_O,
    output logic CPU_MEM_CMD_BUSY_O,

    input logic [WISHBONE_BUS_WIDTH-1:0] CPU_MEM_WBM_DAT_I,
    input logic CPU_MEM_WBM_ERR_I,
    input logic CPU_MEM_WBM_ACK_I,
    output logic CPU_MEM_WBM_CYC_O,
    output logic CPU_MEM_WBM_STB_O,
    output logic [WISHBONE_ADDR_WIDTH-1:0] CPU_MEM_WBM_ADR_O,
    output logic CPU_MEM_WBM_WE_O,
    output logic [WISHBONE_BUS_WIDTH-1:0] CPU_MEM_WBM_DAT_O,
    output logic [WISHBONE_BUS_WIDTH/8-1:0] CPU_MEM_WBM_SEL_O

);
  logic [WISHBONE_ADDR_WIDTH-1:0] cmd_addr_q;
  logic [WISHBONE_BUS_WIDTH-1:0] cmd_wdata_q;
  logic [WISHBONE_BUS_WIDTH/8-1:0] cmd_sel_q;
  logic cmd_we_q;
  logic cmd_busy;

  always_ff @(posedge CLK_I) begin
    if (RST_I) begin
      CPU_MEM_WBM_CYC_O  <= 0;
      CPU_MEM_WBM_STB_O  <= 0;
      cmd_busy <= 0;
      cmd_addr_q <= 0;
      cmd_wdata_q <= 0;
      cmd_sel_q <= 0;
      cmd_we_q <= 0;
    end else begin
          CPU_MEM_WBM_STB_O  <= 0;
        if (CPU_MEM_CMD_START_I && !cmd_busy) begin
          CPU_MEM_WBM_CYC_O  <= 1;
          CPU_MEM_WBM_STB_O  <= 1;
          cmd_busy <= 1;
          cmd_addr_q <= CPU_MEM_CMD_ADDR_I;
          cmd_wdata_q <= CPU_MEM_CMD_WDATA_I;
          cmd_sel_q <= CPU_MEM_CMD_SEL_I;
          cmd_we_q <= CPU_MEM_CMD_WE_I;
        end else if (CPU_MEM_WBM_ACK_I || CPU_MEM_WBM_ERR_I) begin
          CPU_MEM_WBM_CYC_O  <= 0;
          CPU_MEM_WBM_STB_O  <= 0;
          cmd_busy <= 0;
          cmd_addr_q <= 0;
          cmd_wdata_q <= 0;
          cmd_sel_q <= 0;
          cmd_we_q <= 0;
        end 
    end
  end

  assign CPU_MEM_WBM_WE_O = cmd_we_q;
  assign CPU_MEM_WBM_SEL_O = cmd_sel_q;
  assign CPU_MEM_WBM_ADR_O = cmd_addr_q;
  assign CPU_MEM_WBM_DAT_O = cmd_wdata_q;
  assign CPU_MEM_CMD_RDATA_O = CPU_MEM_WBM_DAT_I;
  assign CPU_MEM_CMD_BUSY_O = cmd_busy;

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
  assert property(RST_I |-> ##1 !CPU_MEM_WBM_CYC_O && !CPU_MEM_WBM_STB_O);
  assert property(disable iff (RST_I) CPU_MEM_CMD_START_I && !CPU_MEM_CMD_BUSY_O |-> ##1 CPU_MEM_WBM_CYC_O && CPU_MEM_WBM_STB_O);
  assert property(disable iff (RST_I) CPU_MEM_WBM_STB_O |-> ##1 !CPU_MEM_WBM_STB_O);
`endif
endmodule
