// Single-Port Block RAM No-Change Mode

module imem #(ADDR_WIDTH = 32)(
    input logic CLK,
    input logic EN,
    input logic [9:0] ADDR,
    output logic [31:0] RDATA
);

  logic [31:0] RAM[(2**ADDR_WIDTH-1):0];

  always @(posedge CLK) begin
    if (EN) begin
      RDATA <= RAM[ADDR];
    end
  end
endmodule
