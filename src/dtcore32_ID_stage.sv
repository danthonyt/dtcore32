`include "macros.svh"
module dtcore32_ID_stage (
    input logic clk_i,
    input logic rst_i,
    // IMEM
    input logic [31:0] IMEM_rd_data_i,
    input logic [31:0] IMEM_addr_i,
    // IF signals
    input logic [31:0] IF_pc_plus_4_i,
    // WB signals
    input logic [11:7] WB_dest_reg_i,
    input logic [31:0] WB_result_i,
    input logic WB_reg_wr_en_i,
    // ID signals
    input logic ID_stall_i,
    input logic ID_flush_i,
    output logic [19:15] ID_src_reg_1_o,
    output logic [24:20] ID_src_reg_2_o,
    output logic [11:7] ID_dest_reg_o,
    output logic ID_dmem_read_o,
    output logic [1:0]  ID_result_src_o,
    output logic [1:0]  ID_alu_a_src_o,
    output logic [1:0]  ID_mem_wr_size_o,
    output logic [3:0]  ID_alu_control_o,
    output logic [2:0] ID_load_size_o,
    output logic ID_alu_b_src_o,
    output logic ID_reg_wr_en_o,
    output logic ID_jump_o,
    output logic ID_branch_o,
    output logic ID_pc_target_alu_src_o,
    output logic ID_exception_o,
    output logic [31:0] ID_pc_o,
    output logic [31:0] ID_pc_plus_4_o,
    output logic [31:0] ID_reg_data_1_o,
    output logic [31:0] ID_reg_data_2_o,
    // extend unit
    output logic [31:0] ID_imm_ext_o
  );
  logic [31:0] ID_instr;
  // IF/ID register
  always_ff @(posedge clk_i)
  begin
    if (rst_i || ID_flush_i)
    begin
      ID_instr <= `NOP_INSTRUCTION;
      ID_pc_o <= 0;
      ID_pc_plus_4_o <= 0 ;
    end
    else if (!ID_stall_i)
    begin
      ID_instr <= IMEM_rd_data_i;
      ID_pc_o <= IMEM_addr_i;
      ID_pc_plus_4_o <= IF_pc_plus_4_i;
    end
  end
  // decoder unit
  dtcore32_decode_unit  dtcore32_decode_unit_inst (
                          .clk_i(clk_i),
                          .rst_i(rst_i),
                          .ID_instr_i(ID_instr),
                          .ID_dmem_read_o(ID_dmem_read_o),
                          .ID_result_src_o(ID_result_src_o),
                          .ID_alu_a_src_o(ID_alu_a_src_o),
                          .ID_mem_wr_size_o(ID_mem_wr_size_o),
                          .ID_alu_control_o(ID_alu_control_o),
                          .ID_load_size_o(ID_load_size_o),
                          .ID_alu_b_src_o(ID_alu_b_src_o),
                          .ID_reg_wr_en_o(ID_reg_wr_en_o),
                          .ID_jump_o(ID_jump_o),
                          .ID_branch_o(ID_branch_o),
                          .ID_pc_target_alu_src_o(ID_pc_target_alu_src_o),
                          .ID_exception_o(ID_exception_o),
                          .ID_src_reg_1_o(ID_src_reg_1_o),
                          .ID_src_reg_2_o(ID_src_reg_2_o),
                          .ID_dest_reg_o(ID_dest_reg_o),
                          .ID_imm_ext_o(ID_imm_ext_o)
                        );
  // register file
  dtcore32_regfile  dtcore32_regfile_inst (
                      .clk_i(clk_i),
                      .rst_i(rst_i),
                      .regfile_wr_en_i(WB_reg_wr_en_i),
                      .src_reg_1_i(ID_src_reg_1_o),
                      .src_reg_2_i(ID_src_reg_2_o),
                      .dest_reg_i(WB_dest_reg_i),
                      .reg_wr_data_i(WB_result_i),
                      .src_reg_1_rd_data_o(ID_reg_data_1_o),
                      .src_reg_2_rd_data_o(ID_reg_data_2_o)
                    );


endmodule


