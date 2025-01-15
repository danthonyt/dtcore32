`include "macros.svh"
module dtcore32_EX_MEM_reg
  (
    input logic clk_i,
    input logic rst_i,
    input logic EX_reg_wr_en_i,
    input logic [1:0] EX_result_src_i,
    input logic [2:0] EX_load_size_i,
    input logic [1:0] EX_mem_wr_size_i,
    input logic EX_csr_wr_en_i,
    input logic [31:0] EX_alu_result_i,
    input logic [31:0] EX_dmem_wr_data_i,
    input logic [11:7] EX_dest_reg_i,
    input logic [31:0] EX_pc_plus_4_i,
    input logic [31:0] EX_csr_rd_data_i,
    output logic MEM_reg_wr_en_o,
    output logic [1:0] MEM_result_src_o,
    output logic [2:0] MEM_load_size_o,
    output logic [1:0] MEM_mem_wr_size_o,
    output logic MEM_csr_wr_en_o,
    output logic [31:0] MEM_alu_result_o,
    output logic [31:0] MEM_dmem_wr_data_o,
    output logic [11:7] MEM_dest_reg_o,
    output logic [31:0] MEM_pc_plus_4_o,
    output logic [31:0] MEM_csr_rd_data_o

  );
  always_ff @(posedge clk_i)
  begin
    if (rst_i)
    begin
      MEM_reg_wr_en_o <= 0;
      MEM_result_src_o <= 0;
      MEM_load_size_o <= 0;
      MEM_mem_wr_size_o <= 0;
      MEM_csr_wr_en_o <= 0;
      MEM_alu_result_o <= 0;
      MEM_dmem_wr_data_o <= 0;
      MEM_dest_reg_o <= 0;
      MEM_pc_plus_4_o <= 0;
      MEM_csr_rd_data_o <= 0;
    end
    else
    begin
      MEM_reg_wr_en_o <= EX_reg_wr_en_i;
      MEM_result_src_o <= EX_result_src_i;
      MEM_load_size_o <= EX_load_size_i;
      MEM_mem_wr_size_o <= EX_mem_wr_size_i;
      MEM_csr_wr_en_o <= EX_csr_wr_en_i;
      MEM_alu_result_o <= EX_alu_result_i;
      MEM_dmem_wr_data_o <= EX_dmem_wr_data_i;
      MEM_dest_reg_o <= EX_dest_reg_i;
      MEM_pc_plus_4_o <= EX_pc_plus_4_i;
      MEM_csr_rd_data_o <= EX_csr_rd_data_i;
    end
  end
endmodule
