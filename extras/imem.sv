// Single-Port Block RAM No-Change Mode

module imem (
    input logic clk_i,
    input logic en_i,
    input logic [9:0] addr_i,
    output logic [31:0] rdata_o
);

  logic [31:0] RAM  [1023:0];

  always @(posedge clk_i) begin
    if (en_i) begin
      rdata_o <= RAM[addr_i];
    end
  end
endmodule
