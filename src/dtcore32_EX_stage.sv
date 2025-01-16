`include "macros.svh"
module dtcore32_EX_stage (
    input logic clk_i,
    input logic rst_i,
    input logic EX_jump_i,
    input logic EX_branch_i,
    input logic [3:0] EX_alu_control_i,
    input logic [1:0] EX_alu_b_src_i,
    input logic [1:0] EX_alu_a_src_i,
    input logic EX_pc_target_alu_src_i,
    input logic [31:0] EX_reg_data_1_i,
    input logic [31:0] EX_reg_data_2_i,
    input logic [31:0] EX_pc_i,
    input logic [31:0] EX_imm_ext_i,
    input logic [1:0] EX_forward_a_i,
    input logic [1:0] EX_forward_b_i,
    input logic [31:0] EX_csr_rd_data_i,
    input logic [31:0] MEM_alu_result_i,
    input logic [31:0] WB_result_i,
    input logic MEM_stall_i,
    // pipeline in
    input logic EX_reg_wr_en_i,
    input logic [1:0] EX_result_src_i,
    input logic [2:0] EX_load_size_i,
    input logic [1:0] EX_mem_wr_size_i,
    input logic EX_csr_wr_en_i,
    input logic [31:0] EX_alu_result_i,
    input logic [31:0] EX_dmem_wr_data_i,
    input logic [11:7] EX_dest_reg_i,
    input logic [31:0] EX_pc_plus_4_i,
    output logic EX_pc_src_o,
    output logic [31:0] EX_alu_result_o,
    output logic [31:0] EX_dmem_wr_data_o,
    output logic [31:0] EX_pc_target_o,
    // pipeline out 
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

  logic MEM_reg_wr_en;
  logic [1:0] MEM_result_src;
  logic [2:0] MEM_load_size;
  logic [1:0] MEM_mem_wr_size;
  logic MEM_csr_wr_en;
  logic [31:0] MEM_alu_result;
  logic [31:0] MEM_dmem_wr_data;
  logic [11:7] MEM_dest_reg;
  logic [31:0] MEM_pc_plus_4;
  logic [31:0] MEM_csr_rd_data;

  logic EX_pc_src;
  logic [31:0] EX_alu_result;
  logic [31:0] EX_dmem_wr_data;
  logic [31:0] EX_pc_target;

  logic [31:0] EX_src_a_tick;
  logic [31:0] EX_src_a;
  logic [31:0] EX_src_b;
  logic [31:0] EX_pc_target_src_a;
  logic EX_branch_cond;
  mux3to1 # (
            .WIDTH(32)
          )
          mux3to1_inst_EX1 (
            .in0(EX_reg_data_1_i),
            .in1(WB_result_i),
            .in2(MEM_alu_result_i),
            .sel(EX_forward_a_i),
            .out(EX_src_a_tick)
          );
  mux4to1 # (
            .WIDTH(32)
          )
          mux4to1_inst_EX2 (
            .in0(EX_src_a_tick),
            .in1(32'd0),
            .in2(EX_pc_i),
            .in3(EX_imm_ext_i),
            .sel(EX_alu_a_src_i),
            .out(EX_src_a)
          );
  mux3to1 # (
            .WIDTH(32)
          )
          mux3to1_inst_EX2 (
            .in0(EX_reg_data_2_i),
            .in1(WB_result_i),
            .in2(MEM_alu_result_i),
            .sel(EX_forward_b_i),
            .out(EX_dmem_wr_data)
          );
  mux4to1 # (
            .WIDTH(32)
          )
          mux3to1_inst_EX3 (
            .in0(EX_dmem_wr_data),
            .in1(EX_imm_ext_i),
            .in2(EX_csr_rd_data_i),
            .in3(32'd0),
            .sel(EX_alu_b_src_i),
            .out(EX_src_b)
          );
  mux2to1 # (
            .WIDTH(32)
          )
          mux2to1_inst_EX2 (
            .in0(EX_pc_i),
            .in1(EX_src_a_tick),
            .sel(EX_pc_target_alu_src_i),
            .out(EX_pc_target_src_a)
          );
  adder # (
          .WIDTH(32)
        )
        adder_inst_EX (
          .in1(EX_pc_target_src_a),
          .in2(EX_imm_ext_i),
          .sum(EX_pc_target)
        );
  dtcore32_alu # (
                 .WIDTH(32)
               )
               dtcore32_alu_inst (
                 .control(EX_alu_control_i),
                 .a(EX_src_a),
                 .b(EX_src_b),
                 .y(EX_alu_result),
                 .BranchCond(EX_branch_cond)
               );
  assign EX_pc_src = EX_jump_i | (EX_branch_i & EX_branch_cond);
  assign EX_pc_src_o =  EX_pc_src;
  assign EX_alu_result_o =  EX_alu_result;
  assign EX_dmem_wr_data_o =  EX_dmem_wr_data;
  assign EX_pc_target_o =  EX_pc_target;

  always_ff @(posedge clk_i)
  begin
    if (rst_i)
    begin
      MEM_reg_wr_en <= 0;
      MEM_result_src <= 0;
      MEM_load_size <= 0;
      MEM_mem_wr_size <= 0;
      MEM_csr_wr_en <= 0;
      MEM_alu_result <= 0;
      MEM_dmem_wr_data <= 0;
      MEM_dest_reg <= 0;
      MEM_pc_plus_4 <= 0;
      MEM_csr_rd_data <= 0;
    end
    else if (!MEM_stall_i)
    begin
      MEM_reg_wr_en <= EX_reg_wr_en_i;
      MEM_result_src <= EX_result_src_i;
      MEM_load_size <= EX_load_size_i;
      MEM_mem_wr_size <= EX_mem_wr_size_i;
      MEM_csr_wr_en <= EX_csr_wr_en_i;
      MEM_alu_result <= EX_alu_result_i;
      MEM_dmem_wr_data <= EX_dmem_wr_data_i;
      MEM_dest_reg <= EX_dest_reg_i;
      MEM_pc_plus_4 <= EX_pc_plus_4_i;
      MEM_csr_rd_data <= EX_csr_rd_data_i;
    end
  end

  assign MEM_reg_wr_en_o = MEM_reg_wr_en;
  assign  MEM_result_src_o = MEM_result_src;
  assign MEM_load_size_o = MEM_load_size;
  assign  MEM_mem_wr_size_o = MEM_mem_wr_size;
  assign MEM_csr_wr_en_o = MEM_csr_wr_en;
  assign  MEM_alu_result_o = MEM_alu_result;
  assign  MEM_dmem_wr_data_o = MEM_dmem_wr_data;
  assign  MEM_dest_reg_o = MEM_dest_reg;
  assign  MEM_pc_plus_4_o = MEM_pc_plus_4;
  assign  MEM_csr_rd_data_o = MEM_csr_rd_data;
endmodule
