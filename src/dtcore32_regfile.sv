module dtcore32_regfile(
    input  logic           clk_i,
    input  logic rst_i,
    input  logic 		      regfile_wr_en_i,

    input  logic     [4:0]  src_reg_1_i,
    input  logic     [4:0]  src_reg_2_i,
    input  logic     [4:0]   dest_reg_i,
    input  logic     [31:0]  reg_wr_data_i,
    output logic     [31:0] src_reg_1_rd_data_o,
    output logic     [31:0] src_reg_2_rd_data_o
  );
  // ===========================================================================
  // 			          Parameters, Registers, and Wires
  // ===========================================================================

  // ===========================================================================
  // 			          Instantiations
  // ===========================================================================

  // ===========================================================================
  // 			          Implementation
  // ===========================================================================
  integer i;
  logic     [31:0] src_reg_1_rd_data;
  logic     [31:0] src_reg_2_rd_data;
  logic [31:0] reg_array[0:31];
  logic [31:0] zero;
  logic [31:0] ra;
  logic [31:0] sp;
  logic [31:0] gp;
  logic [31:0] tp;
  logic [31:0] t0;
  logic [31:0] t1;
  logic [31:0] t2;
  logic [31:0] fp;
  logic [31:0] s1;
  logic [31:0] a0;
  logic [31:0] a1;
  logic [31:0] a2;
  logic [31:0] a3;
  logic [31:0] a4;
  logic [31:0] a5;
  logic [31:0] a6;
  logic [31:0] a7;
  logic [31:0] s2;
  logic [31:0] s3;
  logic [31:0] s4;
  logic [31:0] s5;
  logic [31:0] s6;
  logic [31:0] s7;
  logic [31:0] s8;
  logic [31:0] s9;
  logic [31:0] s10;
  logic [31:0] s11;
  logic [31:0] t3;
  logic [31:0] t4;
  logic [31:0] t5;
  logic [31:0] t6;

  // register names for debugging
  assign zero = reg_array[0];
  assign ra = reg_array[1];
  assign sp = reg_array[2];
  assign gp = reg_array[3];
  assign tp = reg_array[4];
  assign t0 = reg_array[5];
  assign t1 = reg_array[6];
  assign t2 = reg_array[7];
  assign fp = reg_array[8];
  assign s1 = reg_array[9];
  assign a0 = reg_array[10];
  assign a1 = reg_array[11];
  assign a2 = reg_array[12];
  assign a3 = reg_array[13];
  assign a4 = reg_array[14];
  assign a5 = reg_array[15];
  assign a6 = reg_array[16];
  assign a7 = reg_array[17];
  assign s2 = reg_array[18];
  assign s3 = reg_array[19];
  assign s4 = reg_array[20];
  assign s5 = reg_array[21];
  assign s6 = reg_array[22];
  assign s7 = reg_array[23];
  assign s8 = reg_array[24];
  assign s9 = reg_array[25];
  assign s10 = reg_array[26];
  assign s11 = reg_array[27];
  assign t3 = reg_array[28];
  assign t4 = reg_array[29];
  assign t5 = reg_array[30];
  assign t6 = reg_array[31];
  assign reg_array[0] = 32'd0;
  // three ported register file
  // read two ports combinationally (A1/RD1, A2/RD2)
  // write third port on rising edge of clock (A3/WD3/WE3)
  // register 0 hardwired to 0
  always_ff @(negedge clk_i)
  begin
    if (rst_i)
    begin
      for (i = 1; i < 32; i = i + 1)
        reg_array[i] <= 32'd0;
    end
    else if (regfile_wr_en_i)
    begin
      if (dest_reg_i != 0)
        reg_array[dest_reg_i] <= reg_wr_data_i;
    end
  end
  assign src_reg_1_rd_data = (src_reg_1_i != 0) ? reg_array[src_reg_1_i] : 0;
  assign src_reg_2_rd_data = (src_reg_2_i != 0) ? reg_array[src_reg_2_i] : 0;

  assign src_reg_1_rd_data_o = src_reg_1_rd_data;
  assign src_reg_2_rd_data_o = src_reg_2_rd_data;
endmodule

