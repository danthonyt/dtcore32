module dtcore32_ID_stage (
    input logic clk_i,
    input logic rst_i,
    input logic [31:0] ID_instr_i,
    input logic WB_reg_wr_en_i,
    input logic WB_csr_wr_en_i,
    input logic [11:7] WB_dest_reg_i,
    input logic [31:0] WB_result_i,
    input logic [31:0] WB_csr_wr_data_i,

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
    output logic ID_exception_o

  );
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
                      .clk(clk_i),
                      .we3(WB_reg_wr_en_i),
                      .rst(rst_i),
                      .a1(ID_src_reg_1),
                      .a2(ID_src_reg_2),
                      .a3(WB_dest_reg_i),
                      .wd3(WB_result_i),
                      .rd1(ID_reg_data_1),
                      .rd2(ID_reg_data_2)
                    );

  extend  extend_inst (
            .instr_data(ID_instr_i[31:7]),
            .imm_src(ID_imm_src),
            .imm_ext(ID_imm_ext_sig)
          );

          dtcore32_controller  dtcore32_controller_inst (
            .clk_i(clk_i),
            .rst_i(rst_i),
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
endmodule


