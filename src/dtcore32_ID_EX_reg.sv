`include "macros.svh"
module dtcore32_ID_EX_reg
  (
    input logic clk_i,
    input logic rst_i,
    input logic EX_flush_i,
    input logic ID_reg_wr_en_i,
    input logic [1:0] ID_result_src_i,
    input logic [2:0] ID_load_size_i,
    input logic [1:0] ID_mem_wr_size_i,
    input logic ID_jump_i,
    input logic ID_branch_i,
    input logic [3:0] ID_alu_control_i,
    input logic ID_alu_b_src_i,
    input logic [1:0] ID_alu_a_src_i,
    input logic ID_pc_target_alu_src_i,
    input logic ID_csr_wr_en_i,
    input logic [31:0] ID_reg_data_1_i,
    input logic [31:0] ID_reg_data_2_i,
    input logic [31:0] ID_pc_i,
    input logic [19:15] ID_src_reg_1_i,
    input logic [24:20] ID_src_reg_2_i,
    input logic [11:7] ID_dest_reg_i,
    input logic [31:0] ID_imm_ext_i,
    input logic [31:0] ID_pc_plus_4_i,
    input logic [31:0] ID_csr_rd_data_i,
    output logic EX_reg_wr_en_o,
    output logic [1:0] EX_result_src_o,
    output logic [2:0] EX_load_size_o,
    output logic [1:0] EX_mem_wr_size_o,
    output logic EX_jump_o,
    output logic EX_branch_o,
    output logic [3:0] EX_alu_control_o,
    output logic EX_alu_b_src_o,
    output logic [1:0] EX_alu_a_src_o,
    output logic EX_pc_target_alu_src_o,
    output logic EX_csr_wr_en_o,
    output logic [31:0] EX_reg_data_1_o,
    output logic [31:0] EX_reg_data_2_o,
    output logic [31:0] EX_pc_o,
    output logic [19:15] EX_src_reg_1_o,
    output logic [24:20] EX_src_reg_2_o,
    output logic [11:7] EX_dest_reg_o,
    output logic [31:0] EX_imm_ext_o,
    output logic [31:0] EX_pc_plus_4_o,
    output logic [31:0] EX_csr_rd_data_o
  );
  always_ff @(posedge clk_i)
  begin
    if (rst_i || EX_flush_i)
    begin
      EX_reg_wr_en_o <= 0;
      EX_result_src_o <= 0;
      EX_load_size_o <= 0;
      EX_mem_wr_size_o <= 0;
      EX_jump_o <= 0;
      EX_branch_o <= 0;
      EX_alu_control_o <= 0;
      EX_alu_a_src_o <= 0;
      EX_alu_b_src_o <= 1;
      EX_pc_target_alu_src_o <= 0;
      EX_reg_data_1_o <= 0;
      EX_reg_data_2_o <= 0;
      EX_pc_o <= 0;
      EX_src_reg_1_o <= 0;
      EX_src_reg_2_o <= 0;
      EX_dest_reg_o <= 0;
      EX_imm_ext_o <= 0;
      EX_pc_plus_4_o <= 0;
      EX_csr_wr_en_o <= 0;
      EX_csr_rd_data_o <= 0;
    end
    else
    begin
      EX_reg_wr_en_o <= ID_reg_wr_en_i;
      EX_result_src_o <= ID_result_src_i;
      EX_load_size_o <= ID_load_size_i;
      EX_mem_wr_size_o <= ID_mem_wr_size_i;
      EX_jump_o <= ID_jump_i;
      EX_branch_o <= ID_branch_i;
      EX_alu_control_o <= ID_alu_control_i;
      EX_alu_a_src_o <= ID_alu_a_src_i;
      EX_alu_b_src_o <= ID_alu_b_src_i;
      EX_pc_target_alu_src_o <= ID_pc_target_alu_src_i;
      EX_reg_data_1_o <= ID_reg_data_1_i;
      EX_reg_data_2_o <= ID_reg_data_2_i;
      EX_pc_o <= ID_pc_i;
      EX_src_reg_1_o <= ID_src_reg_1_i;
      EX_src_reg_2_o <= ID_src_reg_2_i;
      EX_dest_reg_o <= ID_dest_reg_i;
      EX_imm_ext_o <= ID_imm_ext_i;
      EX_pc_plus_4_o <= ID_pc_plus_4_i;
      EX_csr_wr_en_o <= ID_csr_wr_en_i;
      EX_csr_rd_data_o <= ID_csr_rd_data_i;
    end
  end
endmodule
