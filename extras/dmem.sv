module dmem #(ADDR_WIDTH = 32)(
    input logic CLK,
    input logic [3:0] WE,
    input logic EN,
    input logic [ADDR_WIDTH-1:0] ADDR,
    input logic [31:0] WDATA,
    output logic [31:0] RDATA
);

  logic [31:0] RAM[(2**ADDR_WIDTH-1):0];

  integer i;
  always @(posedge CLK) begin
    if (EN) begin
      for (i = 0; i < 4; i = i + 1) begin
        if (WE[i]) RAM[ADDR][i*8+:8] <= WDATA[i*8+:8];
      end
    end
    RDATA <= RAM[ADDR];
  end
endmodule
