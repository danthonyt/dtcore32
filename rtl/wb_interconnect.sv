module wb_interconnect #(
    parameter WISHBONE_ADDR_WIDTH = 32,
    parameter WISHBONE_BUS_WIDTH  = 32
) (
    // interface to master wishbone slave
    output logic [WISHBONE_BUS_WIDTH-1:0] WBM_DAT_I,
    output logic WBM_ERR_I,
    output logic WBM_ACK_I,
    input logic WBM_CYC_O,
    input logic WBM_STB_O,
    input logic [WISHBONE_ADDR_WIDTH-1:0] WBM_ADR_O,
    input logic WBM_WE_O,
    input logic [WISHBONE_BUS_WIDTH-1:0] WBM_DAT_O,
    input logic [WISHBONE_BUS_WIDTH/8-1:0] WBM_SEL_O,

    // connected to all slaves
    output logic [WISHBONE_ADDR_WIDTH-1:0] WBS_ADR_I,
    output logic WBS_WE_I,
    output logic [WISHBONE_BUS_WIDTH-1:0] WBS_DAT_I,
    output logic [WISHBONE_BUS_WIDTH/8-1:0] WBS_SEL_I,

    // interface to dmem wishbone slave - standard mode
    output logic DMEM_WBS_CYC_I,
    output logic DMEM_WBS_STB_I,

    input logic [WISHBONE_BUS_WIDTH-1:0] DMEM_WBS_DAT_O,
    input logic DMEM_WBS_ACK_O,
    input logic DMEM_WBS_ERR_O,

    // interface to uart wishbone slave
    output logic UART_WBS_CYC_I,
    output logic UART_WBS_STB_I,

    input logic [WISHBONE_BUS_WIDTH-1:0] UART_WBS_DAT_O,
    input logic UART_WBS_ACK_O,
    input logic UART_WBS_ERR_O
);
  // imem adress : 0x0000_0000 - 0x0000_03FF connected to a separate wishbone bus
  // dmem adress : 0x0010_0000 - 0x0010_03FF
  // uart adress : 0x0100_0000 - 0x0100_000F
  // for now, bits [31:16] correspond to peripheral addressing,
  // bits [15:0] correspond to actual wishbone addresses
  logic dmem_sel;
  logic uart_sel;
  assign dmem_sel = WBM_ADR_O[31:16] == 16'h0010;
  assign uart_sel = WBM_ADR_O[31:16] == 16'h0100;
  // route cyc, stb, ack, err, and rdata to the proper slave 
  always_comb begin
    WBM_DAT_I = 0;
    WBM_ERR_I = 0;
    WBM_ACK_I = 0;

    DMEM_WBS_CYC_I = 0;
    DMEM_WBS_STB_I = 0;
    UART_WBS_CYC_I = 0;
    UART_WBS_STB_I = 0;
    if (dmem_sel) begin
      WBM_DAT_I = DMEM_WBS_DAT_O;
      WBM_ERR_I = DMEM_WBS_ERR_O;
      WBM_ACK_I = DMEM_WBS_ACK_O;

      DMEM_WBS_CYC_I = WBM_CYC_O;
      DMEM_WBS_STB_I = WBM_STB_O;
      UART_WBS_CYC_I = 0;
      UART_WBS_STB_I = 0;
    end else if (uart_sel) begin
      WBM_DAT_I = UART_WBS_DAT_O;
      WBM_ERR_I = UART_WBS_ERR_O;
      WBM_ACK_I = UART_WBS_ACK_O;

      DMEM_WBS_CYC_I = 0;
      DMEM_WBS_STB_I = 0;
      UART_WBS_CYC_I = WBM_CYC_O;
      UART_WBS_STB_I = WBM_STB_O;
    end
  end


  assign WBS_ADR_I = WBM_ADR_O;
  assign WBS_WE_I  = WBM_WE_O;
  assign WBS_DAT_I = WBM_DAT_O;
  assign WBS_SEL_I = WBM_SEL_O;

  /******************************************/
  //
  //    FORMAL VERIFICATION
  //
  /******************************************/
`ifdef FORMAL
  logic f_clk;
  default clocking @(posedge f_clk);
  endclocking
  assert property (WBM_ADR_O[31:16] == 16'h0010 |-> WBM_DAT_I == DMEM_WBS_DAT_O
      && WBM_ERR_I == DMEM_WBS_ERR_O
      && WBM_ACK_I == DMEM_WBS_ACK_O
      && DMEM_WBS_CYC_I == WBM_CYC_O
      && DMEM_WBS_STB_I == WBM_STB_O
      && UART_WBS_CYC_I == 0
      && UART_WBS_STB_I == 0);

  assert property (WBM_ADR_O[31:16] == 16'h0100 |-> WBM_DAT_I == UART_WBS_DAT_O
      && WBM_ERR_I == UART_WBS_ERR_O
      && WBM_ACK_I == UART_WBS_ACK_O
      && DMEM_WBS_CYC_I == 0
      && DMEM_WBS_STB_I == 0
      && UART_WBS_CYC_I == WBM_CYC_O
      && UART_WBS_STB_I == WBM_STB_O);

`endif

endmodule
