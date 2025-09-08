module regfile (
    input logic clk_i,
    input logic rst_i,

    input logic write_en_i,
    input  logic [ 4:0] rs1_addr_i,
    input  logic [ 4:0] rs2_addr_i,
    input  logic [ 4:0] rd_addr_i,
    input  logic [31:0] reg_wr_data_i,
    output logic [31:0] rs1_rdata_o,
    output logic [31:0] rs2_rdata_o
);
  integer i;
  logic [31:0] reg_array[0:31];

  // three ported register file
  // read two ports combinationally (A1/RD1, A2/RD2)
  // write third port on rising edge of clock (A3/WD3/WE3)
  // register 0 hardwired to 0
  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      for (i = 0; i < 32; i = i + 1) reg_array[i] <= 32'd0;
    end else if (write_en_i)begin
      if (rd_addr_i != 0) reg_array[rd_addr_i] <= reg_wr_data_i;
    end
  end
    assign rs1_rdata_o = reg_array[rs1_addr_i];
    assign rs2_rdata_o = reg_array[rs2_addr_i];

endmodule

