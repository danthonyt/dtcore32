module wb_interconnect #(
    parameter WISHBONE_ADDR_WIDTH = 32,
    parameter WISHBONE_BUS_WIDTH  = 32
) (
    // master signals
    
    input logic wbm_cyc,
    input logic wbm_stb,
    input logic [WISHBONE_ADDR_WIDTH-1:0] wbm_adr,
    input logic wbm_we,
    input logic [WISHBONE_BUS_WIDTH-1:0] wbm_dat_o,
    input logic [WISHBONE_BUS_WIDTH/8-1:0] wbm_sel,
    output logic [WISHBONE_BUS_WIDTH-1:0] wbm_dat_i,
    output logic wbm_err,
    output logic wbm_ack,

    // connected to all slaves
    output logic [WISHBONE_ADDR_WIDTH-1:0] ic_wbs_adr,
    output logic ic_wbs_we,
    output logic [WISHBONE_BUS_WIDTH-1:0] ic_wbs_dat_i,
    output logic [WISHBONE_BUS_WIDTH/8-1:0] ic_wbs_sel,

    // uart slave signals
    output logic uart_wbs_cyc,
    output logic uart_wbs_stb,

    input logic [WISHBONE_BUS_WIDTH-1:0] uart_wbs_dat_o,
    input logic uart_wbs_ack,
    input logic uart_wbs_err
);
  // imem adress : 0x0000_0000 - 0x0000_03FF connected to a separate wishbone bus
  // dmem adress : 0x0010_0000 - 0x0010_03FF
  // uart adress : 0x0100_0000 - 0x0100_000F
  // for now, bits [31:16] correspond to peripheral addressing,
  // bits [15:0] correspond to actual wishbone addresses
  logic uart_sel;
  assign uart_sel = wbm_adr[31:16] == 16'h0100;
  // route cyc, stb, ack, err, and rdata to the proper slave 
  always_comb begin
    wbm_dat_i = 0;
    wbm_err = 0;
    wbm_ack = 0;
    uart_wbs_cyc = 0;
    uart_wbs_stb = 0;
    if (uart_sel) begin
      wbm_dat_i = uart_wbs_dat_o;
      wbm_err = uart_wbs_err;
      wbm_ack = uart_wbs_ack;
      uart_wbs_cyc = wbm_cyc;
      uart_wbs_stb = wbm_stb;
    end
  end


  assign ic_wbs_adr = wbm_adr;
  assign ic_wbs_we  = wbm_we;
  assign ic_wbs_dat_i = wbm_dat_o;
  assign ic_wbs_sel = wbm_sel;

  /******************************************/
  //
  //    FORMAL VERIFICATION
  //
  /******************************************/
`ifdef FORMAL
  logic f_clk;
  default clocking @(posedge f_clk);
  endclocking

  assert property (wbm_adr[31:16] == 16'h0100 |-> wbm_dat_i == uart_wbs_dat_o
      && wbm_err == uart_wbs_err
      && wbm_ack == uart_wbs_ack
      && DMEM_WBS_CYC_I == 0
      && DMEM_WBS_STB_I == 0
      && uart_wbs_cyc == wbm_cyc
      && uart_wbs_stb == wbm_stb);

`endif

endmodule
