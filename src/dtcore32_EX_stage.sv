`include "macros.svh"
module dtcore32_EX_stage (
    input logic clk_i,
    input logic rst_i,

    // ID stage
    input logic ID_dmem_read_i,
    input logic [1:0] ID_result_src_i,
    input logic [2:0] ID_load_size_i,
    input logic [1:0] ID_mem_wr_size_i,
    input logic ID_jump_i,
    input logic ID_branch_i,
    input logic [3:0] ID_alu_control_i,
    input logic  ID_alu_b_src_i,
    input logic [1:0] ID_alu_a_src_i,
    input logic ID_pc_target_alu_src_i,
    input logic [31:0] ID_reg_data_1_i,
    input logic [31:0] ID_reg_data_2_i,
    input logic [31:0] ID_pc_i,
    input logic [19:15] ID_src_reg_1_i,
    input logic [24:20] ID_src_reg_2_i,
    input logic [11:7] ID_dest_reg_i,
    input logic [31:0] ID_imm_ext_i,
    input logic [31:0] ID_pc_plus_4_i,
    input logic ID_reg_wr_en_i,

    // EX stage
    input logic [1:0] EX_forward_a_i,
    input logic [1:0] EX_forward_b_i,
    input logic EX_flush_i,
    input logic EX_stall_i,
    output logic EX_reg_wr_en_o,
    output logic [1:0] EX_result_src_o,
    output logic [2:0] EX_load_size_o,
    output logic [1:0] EX_mem_wr_size_o,
    output logic [4:0] EX_src_reg_1_o,
    output logic [4:0] EX_src_reg_2_o,
    output logic [4:0] EX_dest_reg_o,
    output logic [31:0] EX_pc_plus_4_o,
    output logic [31:0] EX_dmem_wr_data_o,
    output logic EX_dmem_read_o,
    output logic [31:0] EX_alu_result_o,
    output logic EX_pc_src_o,
    output logic [31:0] EX_pc_target_o,

    // MEM stage
    input logic [31:0] MEM_alu_result_i,

    // WB stage
    input logic [31:0] WB_result_i
  );

  logic EX_jump;
  logic EX_branch;
  logic [3:0] EX_alu_control;
  logic  EX_alu_b_src;
  logic [1:0] EX_alu_a_src;
  logic EX_pc_target_alu_src;
  logic [31:0] EX_reg_data_1;
  logic [31:0] EX_reg_data_2;
  logic [31:0] EX_pc;
  logic [31:0] EX_src_a_tick;
  logic [31:0] EX_src_a;
  logic [31:0] EX_src_b;
  logic [31:0] EX_pc_target_src_a;
  logic EX_branch_cond;
  logic [31:0] EX_imm_ext;

  // ID/EX register
  always_ff @(posedge clk_i)
  begin
    if (rst_i || EX_flush_i)
    begin
      EX_reg_wr_en_o <= 0;
      EX_result_src_o <= 0;
      EX_load_size_o <= 0;
      EX_mem_wr_size_o <= 0;
      EX_jump <= 0;
      EX_branch <= 0;
      EX_alu_control <= 0;
      EX_alu_a_src <= 0;
      EX_alu_b_src <= 1;
      EX_pc_target_alu_src <= 0;
      EX_reg_data_1 <= 0;
      EX_reg_data_2 <= 0;
      EX_pc <= 0;
      EX_src_reg_1_o <= 0;
      EX_src_reg_2_o <= 0;
      EX_dest_reg_o <= 0;
      EX_imm_ext <= 0;
      EX_pc_plus_4_o <= 0;
      EX_dmem_read_o <= 0;
    end
    else if (!EX_stall_i)
    begin
      EX_reg_wr_en_o <= ID_reg_wr_en_i;
      EX_result_src_o <= ID_result_src_i;
      EX_load_size_o <= ID_load_size_i;
      EX_mem_wr_size_o <= ID_mem_wr_size_i;
      EX_jump <= ID_jump_i;
      EX_branch <= ID_branch_i;
      EX_alu_control <= ID_alu_control_i;
      EX_alu_a_src <= ID_alu_a_src_i;
      EX_alu_b_src <= ID_alu_b_src_i;
      EX_pc_target_alu_src <= ID_pc_target_alu_src_i;
      EX_reg_data_1 <= ID_reg_data_1_i;
      EX_reg_data_2 <= ID_reg_data_2_i;
      EX_pc <= ID_pc_i;
      EX_src_reg_1_o <= ID_src_reg_1_i;
      EX_src_reg_2_o <= ID_src_reg_2_i;
      EX_dest_reg_o <= ID_dest_reg_i;
      EX_imm_ext <= ID_imm_ext_i;
      EX_pc_plus_4_o <= ID_pc_plus_4_i;
      EX_dmem_read_o <= ID_dmem_read_i;
    end
  end

  assign EX_pc_src_o = EX_jump | (EX_branch & EX_branch_cond);


  // alu input 1 data path
  // select reg 1 data or data forwarded from WB or MEM stage
  always_comb
  begin
    case (EX_forward_a_i)
      2'b00:
        EX_src_a_tick = EX_reg_data_1;
      2'b01:
        EX_src_a_tick = WB_result_i;
      2'b10:
        EX_src_a_tick = MEM_alu_result_i;
      default:
        EX_src_a_tick = 0;
    endcase
  end


  // select data from first mux, zero, or pc
  always_comb
  begin
    case (EX_alu_a_src)
      2'b00:
        EX_src_a = EX_src_a_tick;
      2'b01:
        EX_src_a = 0;
      2'b10:
        EX_src_a = EX_pc;
      default:
        EX_src_a = 0;
    endcase
  end


  // alu input 2 data path
  // select reg 2 data or data forwarded from WB or MEM stage
  always_comb
  begin
    case (EX_forward_b_i)
      2'b00:
        EX_dmem_wr_data_o = EX_reg_data_2;
      2'b01:
        EX_dmem_wr_data_o = WB_result_i;
      2'b10:
        EX_dmem_wr_data_o = MEM_alu_result_i;
      default:
        EX_dmem_wr_data_o = 0;
    endcase
  end
  // select data from first mux, or extended immediate
  always_comb
  begin
    case (EX_alu_b_src)
      1'b0:
        EX_src_b = EX_dmem_wr_data_o;
      1'b1:
        EX_src_b = EX_imm_ext;
      default:
        EX_src_b = 0;
    endcase
  end



  // select base address for branch/jump address, selecting either
  // the current pc or reg1_data.
  always_comb
  begin
    case (EX_pc_target_alu_src)
      1'b0:
        EX_pc_target_src_a = EX_pc;
      1'b1:
        EX_pc_target_src_a = EX_src_a_tick;
      default:
        EX_pc_target_src_a = 0;
    endcase
  end

  assign EX_pc_target_o = EX_pc_target_src_a + EX_imm_ext;

  // alu
  dtcore32_alu # (
    .WIDTH(32)
  )
  dtcore32_alu_inst (
    .control(EX_alu_control),
    .a(EX_src_a),
    .b(EX_src_b),
    .alu_result(EX_alu_result_o),
    .branch_condition(EX_branch_cond)
  );

endmodule
