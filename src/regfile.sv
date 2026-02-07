module regfile (
  // --------------------
  // Clock / reset
  // --------------------
  input  logic        clk_i            ,
  input  logic        rst_i            ,
  // --------------------
  // ID-stage read addresses
  // --------------------
  input  logic [ 4:0] id_rs1_addr      ,
  input  logic [ 4:0] id_rs2_addr      ,
  // --------------------
  // WB-stage write
  // --------------------
  input  logic        wb_q_is_rd_write ,
  input  logic [ 4:0] wb_rd_addr       ,
  input  logic [31:0] wb_rd_wdata      ,
  // --------------------
  // ID-stage read data outputs
  // --------------------
  output logic [31:0] regfile_rs1_rdata,
  output logic [31:0] regfile_rs2_rdata
);
  integer        regfile_idx      ;
  logic     [31:0] regfile_arr[0:31];
  // three ported register file
  // read two ports combinationally (A1/RD1, A2/RD2)
  // write third port on rising edge of clock (A3/WD3/WE3)
  // register 0 hardwired to 0
  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      for (regfile_idx = 0; regfile_idx < 32; regfile_idx = regfile_idx + 1) regfile_arr[regfile_idx] <= 32'd0;
    end else if (wb_q_is_rd_write) begin
      if (wb_rd_addr != 0) regfile_arr[wb_rd_addr] <= wb_rd_wdata;
    end
  end
  assign regfile_rs1_rdata = regfile_arr[id_rs1_addr];
  assign regfile_rs2_rdata = regfile_arr[id_rs2_addr];
endmodule