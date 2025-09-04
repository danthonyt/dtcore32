module rom #(
    parameter MEM_DEPTH = 256
) (
    input logic clk_i,
    input logic [$clog2(MEM_DEPTH)-1+2:2] addr_i,
    output logic [31:0] rdata_o
);
  logic [31:0] MEM[MEM_DEPTH-1:0];

  initial begin
    $readmemh("imem.mem", MEM);
  end
  
  always @(posedge clk_i) begin
          rdata_o <= MEM[addr_i];
  end
endmodule
