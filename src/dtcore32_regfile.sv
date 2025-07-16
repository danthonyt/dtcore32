module dtcore32_regfile(
    input  logic           clk_i,
    input  logic            rst_i,
    input  logic 		      regfile_wr_en_i,

    input  logic     [4:0]  src_reg_1_i,
    input  logic     [4:0]  src_reg_2_i,
    input  logic     [4:0]   dest_reg_i,
    input  logic     [31:0]  reg_wr_data_i,
    output logic     [31:0] src_reg_1_rd_data_o,
    output logic     [31:0] src_reg_2_rd_data_o
  );
  integer i;
  logic [31:0] reg_array[0:31];

  // three ported register file
  // read two ports combinationally (A1/RD1, A2/RD2)
  // write third port on rising edge of clock (A3/WD3/WE3)
  // register 0 hardwired to 0
  always_ff @(negedge clk_i)
  begin
    if (rst_i)
    begin
      for (i = 0; i < 32; i = i + 1)
        reg_array[i] <= 32'd0;
    end
    else if (regfile_wr_en_i)
    begin
      if (dest_reg_i != 0)
      begin
        reg_array[dest_reg_i] <= reg_wr_data_i;
      end
    end
  end
  assign src_reg_1_rd_data_o = (src_reg_1_i != 0) ? reg_array[src_reg_1_i] : 0;
  assign src_reg_2_rd_data_o = (src_reg_2_i != 0) ? reg_array[src_reg_2_i] : 0;

endmodule

