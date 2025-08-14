module dmem (
    input logic clk_i,
    input logic [3:0] we_i,
    input logic en_i,
    input logic [9:0] addr_i,
    input logic [31:0] wdata_i,
    output logic [31:0] rdata_o
);

  logic [31:0] RAM[1023:0];

  integer i;
  always @(posedge clk_i) begin
    if (en_i) begin
      for (i = 0; i < 4; i = i + 1) begin
        if (we_i[i]) RAM[addr_i][i*8+:8] <= wdata_i[i*8+:8];
      end
    end
    rdata_o <= RAM[addr_i];
  end
endmodule
