`include "macros.svh"
module dtcore32_EX_stage (
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
    output logic EX_pc_src_o,
    output logic [31:0] EX_alu_result_o,
    output logic [31:0] EX_dmem_wr_data_o,
    output logic [31:0] EX_pc_target_o

  );
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
endmodule
