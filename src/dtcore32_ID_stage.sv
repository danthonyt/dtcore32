module dtcore32_ID_stage (
    input logic clk_i,
    input logic rst_i,
    input logic [31:0] ID_instr_i,
    input logic WB_reg_wr_en_i,
    input logic WB_csr_wr_en_i,
    input logic [11:7] WB_dest_reg_i,
    input logic [31:0] WB_result_i,
    input logic [31:0] WB_csr_wr_data_i,
    input logic EX_stall_i,
    // pipeline in 
    input logic EX_flush_i,
    input logic ID_reg_wr_en_i,
    input logic [1:0] ID_result_src_i,
    input logic [2:0] ID_load_size_i,
    input logic [1:0] ID_mem_wr_size_i,
    input logic ID_jump_i,
    input logic ID_branch_i,
    input logic [3:0] ID_alu_control_i,
    input logic [1:0] ID_alu_b_src_i,
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

    output logic ID_reg_wr_en_o,
    output logic [1:0] ID_result_src_o,
    output logic [2:0] ID_load_size_o,
    output logic [1:0] ID_mem_wr_size_o,
    output logic ID_jump_o,
    output logic ID_branch_o,
    output logic [3:0] ID_alu_control_o,
    output logic [1:0] ID_alu_b_src_o,
    output logic [1:0] ID_alu_a_src_o,
    output logic ID_pc_target_alu_src_o,
    output logic ID_csr_wr_en_o,
    output logic [31:0] ID_reg_data_1_o,
    output logic [31:0] ID_reg_data_2_o,
    output logic [19:15] ID_src_reg_1_o,
    output logic [24:20] ID_src_reg_2_o,
    output logic [11:7] ID_dest_reg_o,
    output logic [31:0] ID_imm_ext_o,
    output logic [31:0] ID_csr_rd_data_o,
    output logic ID_exception_o,

    // pipeline out
    output logic EX_reg_wr_en_o,
    output logic [1:0] EX_result_src_o,
    output logic [2:0] EX_load_size_o,
    output logic [1:0] EX_mem_wr_size_o,
    output logic EX_jump_o,
    output logic EX_branch_o,
    output logic [3:0] EX_alu_control_o,
    output logic [1:0] EX_alu_b_src_o,
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

  logic EX_reg_wr_en;
  logic [1:0] EX_result_src;
  logic [2:0] EX_load_size;
  logic [1:0] EX_mem_wr_size;
  logic EX_jump;
  logic EX_branch;
  logic [3:0] EX_alu_control;
  logic [1:0] EX_alu_b_src;
  logic [1:0] EX_alu_a_src;
  logic EX_pc_target_alu_src;
  logic EX_csr_wr_en;
  logic [31:0] EX_reg_data_1;
  logic [31:0] EX_reg_data_2;
  logic [31:0] EX_pc;
  logic [19:15] EX_src_reg_1;
  logic [24:20] EX_src_reg_2;
  logic [11:7] EX_dest_reg;
  logic [31:0] EX_imm_ext;
  logic [31:0] EX_pc_plus_4;
  logic [31:0] EX_csr_rd_data;





  logic ID_reg_wr_en;
  logic [1:0] ID_result_src;
  logic [2:0] ID_load_size;
  logic [1:0] ID_mem_wr_size;
  logic ID_jump;
  logic ID_branch;
  logic [3:0] ID_alu_control;
  logic [1:0] ID_alu_b_src;
  logic [1:0] ID_alu_a_src;
  logic ID_pc_target_alu_src;
  logic ID_csr_wr_en;
  logic [31:0] ID_reg_data_1;
  logic [31:0] ID_reg_data_2;
  logic [19:15] ID_src_reg_1;
  logic [24:20] ID_src_reg_2;
  logic [11:7] ID_dest_reg;
  logic [31:0] ID_imm_ext;
  logic [31:0] ID_imm_ext_sig;
  logic [31:0] ID_csr_rd_data;
  logic ID_exception;

  logic [6:0] op;
  logic [2:0] funct3;
  logic funct7b5;
  logic [2:0] ID_imm_src;
  logic ID_csr_rd_en;
  logic ID_is_nop;
  logic [19:15] zicsr_rd;
  logic [11:7] zicsr_rs1;

  assign op = ID_instr_i[6:0];
  assign funct3 = ID_instr_i[14:12];
  assign funct7b5 = ID_instr_i[30];
  assign ID_src_reg_1 = ID_is_nop ? 0 : ID_instr_i[19:15];
  assign ID_src_reg_2 = ID_is_nop ? 0 : ID_instr_i[24:20];
  assign ID_dest_reg = ID_is_nop ? 0 : ID_instr_i[11:7];
  assign ID_imm_ext = ID_is_nop ? 0 : ID_imm_ext_sig;
  assign zicsr_rd = ID_instr_i[19:15];
  assign zicsr_rs1 = ID_instr_i[11:7];

  dtcore32_regfile  dtcore32_regfile_inst (
                      .clk_i(clk_i),
                      .rst_i(rst_i),
                      .regfile_wr_en_i(WB_reg_wr_en_i),
                      .src_reg_1_i(ID_src_reg_1),
                      .src_reg_2_i(ID_src_reg_2),
                      .dest_reg_i(WB_dest_reg_i),
                      .reg_wr_data_i(WB_result_i),
                      .src_reg_1_rd_data_o(ID_reg_data_1),
                      .src_reg_2_rd_data_o(ID_reg_data_2)
                    );

  extend  extend_inst (
            .instr_data(ID_instr_i[31:7]),
            .imm_src(ID_imm_src),
            .imm_ext(ID_imm_ext_sig)
          );

  dtcore32_controller  dtcore32_controller_inst (
                         .clk_i(clk_i),
                         .rst_i(rst_i),
                         .ID_instr_i(ID_instr_i),
                         .op_i(op),
                         .funct3_i(funct3),
                         .funct7b5_i(funct7b5),
                         .zicsr_rs1_i(zicsr_rs1),
                         .zicsr_rd_i(zicsr_rd),
                         .ID_result_src_o(ID_result_src),
                         .ID_alu_a_src_o(ID_alu_a_src),
                         .ID_mem_wr_size_o(ID_mem_wr_size),
                         .ID_alu_control_o(ID_alu_control),
                         .ID_imm_src_o(ID_imm_src),
                         .ID_load_size_o(ID_load_size),
                         .ID_alu_b_src_o(ID_alu_b_src),
                         .ID_reg_wr_en_o(ID_reg_wr_en),
                         .ID_jump_o(ID_jump),
                         .ID_branch_o(ID_branch),
                         .ID_pc_target_alu_src_o(ID_pc_target_alu_src),
                         .ID_is_nop_o(ID_is_nop),
                         .ID_exception_o(ID_exception),
                         .ID_csr_wr_en_o(ID_csr_wr_en),
                         .ID_csr_rd_en_o(ID_csr_rd_en)
                       );


  assign ID_reg_wr_en_o =  ID_reg_wr_en;
  assign ID_result_src_o =  ID_result_src;
  assign ID_load_size_o =  ID_load_size;
  assign ID_mem_wr_size_o =  ID_mem_wr_size;
  assign ID_jump_o = ID_jump;
  assign ID_branch_o =  ID_branch;
  assign ID_alu_control_o = ID_alu_control;
  assign ID_alu_b_src_o =  ID_alu_b_src;
  assign ID_alu_a_src_o = ID_alu_a_src;
  assign ID_pc_target_alu_src_o =  ID_pc_target_alu_src;
  assign ID_csr_wr_en_o = ID_csr_wr_en;
  assign ID_reg_data_1_o = ID_reg_data_1;
  assign ID_reg_data_2_o = ID_reg_data_2;
  assign ID_src_reg_1_o = ID_src_reg_1;
  assign ID_src_reg_2_o = ID_src_reg_2;
  assign ID_dest_reg_o = ID_dest_reg;
  assign ID_imm_ext_o = ID_imm_ext;
  assign ID_csr_rd_data_o =  ID_csr_rd_data;
  assign ID_exception_o = ID_exception;

  always_ff @(posedge clk_i)
  begin
    if (rst_i || EX_flush_i)
    begin
      EX_reg_wr_en <= 0;
      EX_result_src <= 0;
      EX_load_size <= 0;
      EX_mem_wr_size <= 0;
      EX_jump <= 0;
      EX_branch <= 0;
      EX_alu_control <= 0;
      EX_alu_a_src <= 0;
      EX_alu_b_src <= 1;
      EX_pc_target_alu_src <= 0;
      EX_reg_data_1 <= 0;
      EX_reg_data_2 <= 0;
      EX_pc <= 0;
      EX_src_reg_1 <= 0;
      EX_src_reg_2 <= 0;
      EX_dest_reg <= 0;
      EX_imm_ext <= 0;
      EX_pc_plus_4 <= 0;
      EX_csr_wr_en <= 0;
      EX_csr_rd_data <= 0;
    end
    else if (!EX_stall_i)
    begin
      EX_reg_wr_en <= ID_reg_wr_en_i;
      EX_result_src <= ID_result_src_i;
      EX_load_size <= ID_load_size_i;
      EX_mem_wr_size <= ID_mem_wr_size_i;
      EX_jump <= ID_jump_i;
      EX_branch <= ID_branch_i;
      EX_alu_control <= ID_alu_control_i;
      EX_alu_a_src <= ID_alu_a_src_i;
      EX_alu_b_src <= ID_alu_b_src_i;
      EX_pc_target_alu_src <= ID_pc_target_alu_src_i;
      EX_reg_data_1 <= ID_reg_data_1_i;
      EX_reg_data_2 <= ID_reg_data_2_i;
      EX_pc <= ID_pc_i;
      EX_src_reg_1 <= ID_src_reg_1_i;
      EX_src_reg_2 <= ID_src_reg_2_i;
      EX_dest_reg <= ID_dest_reg_i;
      EX_imm_ext <= ID_imm_ext_i;
      EX_pc_plus_4 <= ID_pc_plus_4_i;
      EX_csr_wr_en <= ID_csr_wr_en_i;
      EX_csr_rd_data <= ID_csr_rd_data_i;
    end
  end


  assign EX_reg_wr_en_o = EX_reg_wr_en;
  assign EX_result_src_o = EX_result_src;
  assign EX_load_size_o = EX_load_size;
  assign EX_mem_wr_size_o = EX_mem_wr_size;
  assign EX_jump_o = EX_jump;
  assign EX_branch_o = EX_branch;
  assign EX_alu_control_o = EX_alu_control;
  assign EX_alu_a_src_o = EX_alu_a_src;
  assign EX_alu_b_src_o = EX_alu_b_src;
  assign EX_pc_target_alu_src_o = EX_pc_target_alu_src;
  assign EX_reg_data_1_o = EX_reg_data_1;
  assign EX_reg_data_2_o = EX_reg_data_2;
  assign EX_pc_o = EX_pc;
  assign EX_src_reg_1_o = EX_src_reg_1;
  assign EX_src_reg_2_o = EX_src_reg_2;
  assign EX_dest_reg_o = EX_dest_reg;
  assign EX_imm_ext_o = EX_imm_ext;
  assign EX_pc_plus_4_o = EX_pc_plus_4;
  assign EX_csr_wr_en_o = EX_csr_wr_en;
  assign EX_csr_rd_data_o = EX_csr_rd_data;
endmodule


