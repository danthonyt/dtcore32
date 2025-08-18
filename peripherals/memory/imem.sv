// Single-Port Block RAM No-Change Mode

module imem #(
    ADDR_WIDTH = 10
) (
    input logic CLK,
    input logic EN,
    input logic [ADDR_WIDTH-1:0] ADDR,
    output logic [31:0] RDATA
);


  logic [31:0] RAM[(2**(ADDR_WIDTH-2)-1):0];

  initial begin
    $readmemh("imem.mem", RAM);
  end


  always @(posedge CLK) begin
    if (EN) begin
      RDATA <= {RAM[ADDR[ADDR_WIDTH-1:2]]};
    end
  end
endmodule
