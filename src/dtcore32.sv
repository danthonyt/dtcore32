`include "macros.svh"
module dtcore32(
    input logic           clk_i,
    input logic           rst_i,
    input logic   [31:0]  IMEM_rd_data_i,
    input logic   [31:0]  DMEM_rd_data_i,
    output logic [31:0]   IMEM_addr_o,
    output logic [31:0]   DMEM_addr_o,
    output logic [31:0]   DMEM_wr_data_o,
    output logic [3:0]    DMEM_wr_byte_en_o,
    output logic          exception_o
  );

  logic ID_exception;
  logic MEM_exception;

  assign exception_o = ID_exception | MEM_exception;

  // Instruction fetch signals 
  logic [31:0] IF_pc_plus_4;

  // Instruction decode signals
  logic ID_reg_wr_en;
  logic [1:0] ID_result_src;
  logic [2:0] ID_load_size;
  logic [1:0] ID_mem_wr_size;
  logic ID_jump;
  logic ID_branch;
  logic [3:0] ID_alu_control;
  logic  ID_alu_b_src;
  logic [1:0] ID_alu_a_src;
  logic ID_pc_target_alu_src;
  logic [31:0] ID_reg_data_1;
  logic [31:0] ID_reg_data_2;
  logic [31:0] ID_pc;
  logic [19:15] ID_src_reg_1;
  logic [24:20] ID_src_reg_2;
  logic [11:7] ID_dest_reg;
  logic [31:0] ID_imm_ext;
  logic [31:0] ID_pc_plus_4;
  logic ID_dmem_read;

  // Instruction execute signals
  logic EX_pc_src;
  logic EX_reg_wr_en;
  logic [1:0] EX_result_src;
  logic EX_result_src_b0;
  logic [2:0] EX_load_size;
  logic [1:0] EX_mem_wr_size;
  logic [19:15] EX_src_reg_1;
  logic [24:20] EX_src_reg_2;
  logic [11:7] EX_dest_reg;
  logic [31:0] EX_pc_plus_4;
  logic [31:0] EX_dmem_wr_data;
  logic [31:0] EX_alu_result;
  logic [31:0] EX_pc_target;
  logic EX_dmem_read;

  // data memory signals
  logic MEM_reg_wr_en;
  logic [1:0] MEM_result_src;
  logic [31:0] MEM_alu_result;
  logic [11:7] MEM_dest_reg;
  logic [31:0] MEM_pc_plus_4;
  logic [31:0] MEM_dmem_rd_data;

  // write back signals
  logic WB_reg_wr_en;
  logic [11:7] WB_dest_reg;
  logic [31:0] WB_result;

  // hazard unit signals
  logic IF_stall;
  logic ID_stall;
  logic EX_stall;
  logic MEM_stall;
  logic WB_stall;
  logic ID_flush;
  logic EX_flush;
  logic [1:0] EX_forward_a;
  logic [1:0] EX_forward_b;

  // Instruction Fetch stage
  dtcore32_IF_stage  dtcore32_IF_stage_inst (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .IF_stall_i(IF_stall),
    .EX_pc_target_i(EX_pc_target),
    .EX_pc_src_i(EX_pc_src),
    .IMEM_addr_o(IMEM_addr_o),
    .IF_pc_plus_4_o(IF_pc_plus_4)
  );



  //Instruction Decode stage
  dtcore32_ID_stage  dtcore32_ID_stage_inst (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .IMEM_rd_data_i(IMEM_rd_data_i),
    .IMEM_addr_i(IMEM_addr_o),
    .IF_pc_plus_4_i(IF_pc_plus_4),
    .WB_dest_reg_i(WB_dest_reg),
    .WB_result_i(WB_result),
    .WB_reg_wr_en_i(WB_reg_wr_en),
    .ID_stall_i(ID_stall),
    .ID_flush_i(ID_flush),
    .ID_src_reg_1_o(ID_src_reg_1),
    .ID_src_reg_2_o(ID_src_reg_2),
    .ID_dest_reg_o(ID_dest_reg),
    .ID_dmem_read_o(ID_dmem_read),
    .ID_result_src_o(ID_result_src),
    .ID_alu_a_src_o(ID_alu_a_src),
    .ID_mem_wr_size_o(ID_mem_wr_size),
    .ID_alu_control_o(ID_alu_control),
    .ID_load_size_o(ID_load_size),
    .ID_alu_b_src_o(ID_alu_b_src),
    .ID_reg_wr_en_o(ID_reg_wr_en),
    .ID_jump_o(ID_jump),
    .ID_branch_o(ID_branch),
    .ID_pc_target_alu_src_o(ID_pc_target_alu_src),
    .ID_exception_o(ID_exception),
    .ID_pc_o(ID_pc),
    .ID_pc_plus_4_o(ID_pc_plus_4),
    .ID_reg_data_1_o(ID_reg_data_1),
    .ID_reg_data_2_o(ID_reg_data_2),
    .ID_imm_ext_o(ID_imm_ext)
  );
  // execute stage
  dtcore32_EX_stage  dtcore32_EX_stage_inst (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .ID_dmem_read_i(ID_dmem_read),
    .ID_result_src_i(ID_result_src),
    .ID_load_size_i(ID_load_size),
    .ID_mem_wr_size_i(ID_mem_wr_size),
    .ID_jump_i(ID_jump),
    .ID_branch_i(ID_branch),
    .ID_alu_control_i(ID_alu_control),
    .ID_alu_b_src_i(ID_alu_b_src),
    .ID_alu_a_src_i(ID_alu_a_src),
    .ID_pc_target_alu_src_i(ID_pc_target_alu_src),
    .ID_reg_data_1_i(ID_reg_data_1),
    .ID_reg_data_2_i(ID_reg_data_2),
    .ID_pc_i(ID_pc),
    .ID_src_reg_1_i(ID_src_reg_1),
    .ID_src_reg_2_i(ID_src_reg_2),
    .ID_dest_reg_i(ID_dest_reg),
    .ID_imm_ext_i(ID_imm_ext),
    .ID_pc_plus_4_i(ID_pc_plus_4),
    .ID_reg_wr_en_i(ID_reg_wr_en),
    .EX_forward_a_i(EX_forward_a),
    .EX_forward_b_i(EX_forward_b),
    .EX_flush_i(EX_flush),
    .EX_stall_i(EX_stall),
    .EX_reg_wr_en_o(EX_reg_wr_en),
    .EX_result_src_o(EX_result_src),
    .EX_load_size_o(EX_load_size),
    .EX_mem_wr_size_o(EX_mem_wr_size),
    .EX_src_reg_1_o(EX_src_reg_1),
    .EX_src_reg_2_o(EX_src_reg_2),
    .EX_dest_reg_o(EX_dest_reg),
    .EX_pc_plus_4_o(EX_pc_plus_4),
    .EX_dmem_wr_data_o(EX_dmem_wr_data),
    .EX_dmem_read_o(EX_dmem_read),
    .EX_alu_result_o(EX_alu_result),
    .EX_pc_src_o(EX_pc_src),
    .EX_pc_target_o(EX_pc_target),
    .MEM_alu_result_i(MEM_alu_result),
    .WB_result_i(WB_result)
  );

  // Data Memory stage
  assign DMEM_addr_o = MEM_alu_result;
  dtcore32_MEM_stage  dtcore32_MEM_stage_inst (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .DMEM_rd_data_i(DMEM_rd_data_i),
    .DMEM_wr_data_o(DMEM_wr_data_o),
    .DMEM_wr_byte_en_o(DMEM_wr_byte_en_o),
    .EX_reg_wr_en_i(EX_reg_wr_en),
    .EX_result_src_i(EX_result_src),
    .EX_load_size_i(EX_load_size),
    .EX_mem_wr_size_i(EX_mem_wr_size),
    .EX_alu_result_i(EX_alu_result),
    .EX_dmem_wr_data_i(EX_dmem_wr_data),
    .EX_dest_reg_i(EX_dest_reg),
    .EX_pc_plus_4_i(EX_pc_plus_4),
    .MEM_stall_i(MEM_stall),
    .MEM_reg_wr_en_o(MEM_reg_wr_en),
    .MEM_result_src_o(MEM_result_src),
    .MEM_alu_result_o(MEM_alu_result),
    .MEM_dest_reg_o(MEM_dest_reg),
    .MEM_pc_plus_4_o(MEM_pc_plus_4),
    .MEM_dmem_rd_data_o(MEM_dmem_rd_data),
    .MEM_exception_o(MEM_exception)
  );
  // writeback stage
  dtcore32_WB_stage  dtcore32_WB_stage_inst (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .WB_stall_i(WB_stall),
    .MEM_reg_wr_en_i(MEM_reg_wr_en),
    .MEM_result_src_i(MEM_result_src),
    .DMEM_addr(DMEM_addr_o),
    .MEM_dmem_rd_data_i(MEM_dmem_rd_data),
    .MEM_dest_reg_i(MEM_dest_reg),
    .MEM_pc_plus_4_i(MEM_pc_plus_4),
    .WB_reg_wr_en_o(WB_reg_wr_en),
    .WB_dest_reg_o(WB_dest_reg),
    .WB_result_o(WB_result)
  );

  // Hazard Unit
  assign EX_result_src_b0 = EX_result_src[0];
  dtcore32_hazard_unit  dtcore32_hazard_unit_inst (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .EX_src_reg_1_i(EX_src_reg_1),
    .EX_src_reg_2_i(EX_src_reg_2),
    .MEM_dest_reg_i(MEM_dest_reg),
    .WB_dest_reg_i(WB_dest_reg),
    .MEM_reg_wr_en_i(MEM_reg_wr_en),
    .WB_reg_wr_en_i(WB_reg_wr_en),
    .EX_result_src_b0_i(EX_result_src_b0),
    .ID_src_reg_1_i(ID_src_reg_1),
    .ID_src_reg_2_i(ID_src_reg_2),
    .EX_dest_reg_i(EX_dest_reg),
    .EX_dmem_read_i(EX_dmem_read),
    .EX_pc_src_i(EX_pc_src),
    .EX_forward_a_o(EX_forward_a),
    .EX_forward_b_o(EX_forward_b),
    .IF_stall_o(IF_stall),
    .ID_stall_o(ID_stall),
    .EX_flush_o(EX_flush),
    .ID_flush_o(ID_flush),
    .EX_stall_o(EX_stall),
    .MEM_stall_o(MEM_stall),
    .WB_stall_o(WB_stall)
  );
endmodule
