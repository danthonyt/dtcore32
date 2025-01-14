module dtcore32_MEM_WB_reg
  (
    input logic clk_i,
    input logic rst_i,
    input logic MEM_reg_wr_en_i,
    input logic [1:0] MEM_result_src_i,
    input logic MEM_csr_wr_en_i,
    input logic [31:0] MEM_alu_result_i,
    input logic [31:0] MEM_dmem_rd_data_i,
    input logic [11:7] MEM_dest_reg_i,
    input logic [31:0] MEM_pc_plus_4_i,
    input logic [31:0] MEM_csr_rd_data_i,
    output logic WB_reg_wr_en_o,
    output logic [1:0] WB_result_src_o,
    output logic WB_csr_wr_en_o,
    output logic [31:0] WB_alu_result_o,
    output logic [31:0] WB_dmem_rd_data_o,
    output logic [11:7] WB_dest_reg_o,
    output logic [31:0] WB_pc_plus_4_o,
    output logic [31:0] WB_csr_rd_data_o

  );
  always_ff@(posedge clk_i)
  begin
    if(rst_i)
    begin
      WB_reg_wr_en_o <= 0;
      WB_result_src_o <= 0;
      WB_csr_wr_en_o <= 0;
      WB_alu_result_o <= 0;
      WB_dmem_rd_data_o <= 0;
      WB_dest_reg_o <= 0;
      WB_pc_plus_4_o <= 0;
      WB_csr_rd_data_o <= 0;
    end
    else
    begin
      WB_reg_wr_en_o <= MEM_reg_wr_en_i;
      WB_result_src_o <= MEM_result_src_i;
      WB_csr_wr_en_o <= MEM_csr_wr_en_i;
      WB_alu_result_o <= MEM_alu_result_i;
      WB_dmem_rd_data_o <= MEM_dmem_rd_data_i;
      WB_dest_reg_o <= MEM_dest_reg_i;
      WB_pc_plus_4_o <= MEM_pc_plus_4_i;
      WB_csr_rd_data_o <= MEM_csr_rd_data_i;
    end
  end
endmodule
