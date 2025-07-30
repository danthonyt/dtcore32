module dtcore32_dmem (
    input logic clk_i,
    input logic rst_i,
    input logic [3:0] DMEM_wr_byte_en_i,
    input logic [31:0] DMEM_wr_data_i,
    input logic [31:0] DMEM_addr_i,
    output logic [31:0] DMEM_rd_data_o
  );

  parameter DMEM_DEPTH = 32'h0_1000;
  logic [31:0] DMEM[0:DMEM_DEPTH];
  always_ff@(posedge clk_i)
  begin//write
    if (rst_i)
    begin
      DMEM_rd_data_o <= 0;
    end
    else
    begin
      DMEM_rd_data_o <= DMEM[DMEM_addr_i[31:2]];
      if (DMEM_wr_byte_en_i[0])
        DMEM[DMEM_addr_i[31:2]][7:0]   <= DMEM_wr_data_i[7:0];
      if (DMEM_wr_byte_en_i[1])
        DMEM[DMEM_addr_i[31:2]][15:8]   <= DMEM_wr_data_i[15:8];
      if (DMEM_wr_byte_en_i[2])
        DMEM[DMEM_addr_i[31:2]][23:16]   <= DMEM_wr_data_i[23:16];
      if (DMEM_wr_byte_en_i[3])
        DMEM[DMEM_addr_i[31:2]][31:24]   <= DMEM_wr_data_i[31:24];
    end

  end

  initial
    $readmemh("add_dmem.mem",DMEM);


endmodule
