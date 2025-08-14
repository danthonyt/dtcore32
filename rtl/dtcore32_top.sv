module dtcore32_top (
    input logic clk_i,
    input logic rst_i

);

localparam IMEM_WIDTH = 10;
localparam DMEM_WIDTH = 10;
logic [IMEM_WIDTH-1:0] IMEM_addr;
logic [DMEM_WIDTH-1:0] DMEM_addr;
logic [31:0] IMEM_rdata;
logic [31:0] DMEM_rdata;
logic [31:0] DMEM_wdata;
logic [3:0] DMEM_wmask;

imem  imem_inst (
    .clk_i(clk_i),
    .en_i(1),
    .addr_i(IMEM_addr),
    .rdata_o(IMEM_rdata)
  );

dmem  dmem_inst (
    .clk_i(clk_i),
    .we_i(DMEM_wmask),
    .en_i(1),
    .addr_i(DMEM_addr),
    .wdata_i(DMEM_wdata),
    .rdata_o(DMEM_rdata)
  );

dtcore32  dtcore32_inst (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .IMEM_rdata_i(IMEM_rdata),
    .DMEM_rdata_i(DMEM_rdata),
    .IMEM_addr_o(IMEM_addr),
    .DMEM_addr_o(DMEM_addr),
    .DMEM_wdata_o(DMEM_wdata),
    .DMEM_wmask_o(DMEM_wmask)
  );
endmodule