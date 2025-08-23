module dmem #(
    ADDR_WIDTH = 10
) (
    input logic CLK,
    input logic [3:0] WE,
    input logic EN,
    input logic [ADDR_WIDTH-1:0] ADDR,
    input logic [31:0] WDATA,
    output logic [31:0] RDATA,
    output logic RVALID
);

  logic [31:0] RAM[(2**(ADDR_WIDTH-2)-1):0];
  logic [31:0] prev_addr;
  `define LOAD_DMEM

`ifdef LOAD_DMEM
  initial begin
    $readmemh("dmem.mem", RAM);
  end
`endif

  integer i;
  always @(posedge CLK) begin
    if (EN) begin
      for (i = 0; i < 4; i = i + 1) begin
        if (WE[i]) RAM[ADDR[ADDR_WIDTH-1:2]][i*8+:8] <= WDATA[i*8+:8];
      end
    end
    RDATA <= RAM[ADDR[ADDR_WIDTH-1:2]];
  end

  always @(posedge CLK) begin
    prev_addr <= ADDR;
  end

assign RVALID = EN && !WE && (prev_addr == ADDR);
endmodule
