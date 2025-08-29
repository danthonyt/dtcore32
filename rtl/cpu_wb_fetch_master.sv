// uses the wishbone B4 pipelined
module cpu_wb_fetch_master #(
    parameter WISHBONE_ADDR_WIDTH = 32,
    parameter WISHBONE_BUS_WIDTH  = 32
) (
    input logic CLK_I,
    input logic RST_I,
    input logic [WISHBONE_ADDR_WIDTH-1:0] CPU_FETCH_CMD_ADDR_I,
    output logic [WISHBONE_BUS_WIDTH-1:0] CPU_FETCH_CMD_RDATA_O,
    output logic CPU_FETCH_CMD_RDATA_VALID_O,

    input logic [WISHBONE_BUS_WIDTH-1:0] CPU_FETCH_WBM_DAT_I,
    output logic CPU_FETCH_WBM_CYC_O,
    output logic CPU_FETCH_WBM_STB_O,
    output logic [WISHBONE_ADDR_WIDTH-1:0] CPU_FETCH_WBM_ADR_O

);

  // assumes that the instruction memory can read every cycle
  // ack and stall signals can be ignored in this case
  always_ff @(posedge CLK_I) begin
    if (RST_I) begin
      CPU_FETCH_WBM_CYC_O   <= 1;
      CPU_FETCH_WBM_STB_O   <= 1;
      CPU_FETCH_CMD_RDATA_VALID_O <= 0;
    end else begin
      CPU_FETCH_WBM_CYC_O   <= 1;
      CPU_FETCH_WBM_STB_O   <= 1;
      CPU_FETCH_CMD_RDATA_VALID_O <= 1;
    end
  end

  assign CPU_FETCH_CMD_RDATA_O = CPU_FETCH_WBM_DAT_I;
  assign CPU_FETCH_WBM_ADR_O = CPU_FETCH_CMD_ADDR_I;

  /******************************************/
  //
  //    FORMAL VERIFICATION
  //
  /******************************************/
`ifdef FORMAL
  default clocking @(posedge CLK_I);
  endclocking
  // data is invalid the first clock edge after reset is asserted 
  assert property (RST_I |-> ##1 !CPU_FETCH_RDATA_VALID_O);
  // // data is valid otherwise
  assert property (!RST_I |-> ##1 CPU_FETCH_RDATA_VALID_O);


`endif
endmodule
