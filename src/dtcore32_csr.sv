module dtcore32_csr(
    input  logic           clk_i,
    input logic [11:0]      csr_addr_i,
    input logic csr_rd_en_i,
    input logic csr_wr_en_i,
    output logic [31:0]     csr_rd_data_o,
  );
assign rd_en_i = 
// csr [11:10] = 11 is read only, else read/write
// csr [9:8] = lowest priv level that can access csr 
endmodule
