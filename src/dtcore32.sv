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


  // CHECK
  
  logic exception;
  logic misaligned_store;
  logic misaligned_load;
  logic unknown_load;
  // NOP for system calls
  assign exception_o = exception | misaligned_store | misaligned_load | unknown_load;

  // DMEM interface
  logic [31:0] DMEM_addr;
  logic [31:0] DMEM_wr_data;
  logic [3:0]  DMEM_wr_byte_en;
  //logic [31:0] DMEM_rd_data;

  // IMEM interface
  logic [31:0] IMEM_addr;
  //logic [31:0] IMEM_rd_data;

  // Instruction Fetch signals
  logic [31:0] IF_pc_tick;
  logic [31:0] IF_pc_plus_4;

  // Instruction decode signals
  logic [31:0] ID_instr;
  logic ID_reg_wr;
  logic [1:0] ID_result_src;
  logic [2:0] ID_load_size;
  logic [1:0] ID_mem_wr_size;
  logic ID_jump;
  logic ID_branch;
  logic [3:0] ID_alu_control;
  logic ID_alu_b_src;
  logic [1:0] ID_alu_a_src;
  logic ID_pc_target_alu_src;
  logic [2:0] ID_imm_src;
  logic [31:0] ID_reg_data_1;
  logic [31:0] ID_reg_data_2;
  logic [31:0] ID_pc;
  logic [19:15] ID_src_reg_1;
  logic [24:20] ID_src_reg_2;
  logic [11:7] ID_dest_reg;
  logic [31:0] ID_imm_ext;
  logic [31:0] ID_imm_ext_sig;
  logic [31:0] ID_pc_plus_4;
  logic ID_is_nop;

  // Instruction execute signals
  logic EX_pc_src;
  logic EX_branch_cond;
  logic EX_reg_wr;
  logic [1:0] EX_result_src;
  logic [2:0] EX_load_size;
  logic [1:0] EX_mem_wr_size;
  logic EX_jump;
  logic EX_branch;
  logic [3:0] EX_alu_control;
  logic [1:0] EX_alu_b_src;
  logic [1:0] EX_alu_a_src;
  logic EX_pc_target_alu_src;
  logic [31:0] EX_reg_data_1;
  logic [31:0] EX_reg_data_2;
  logic [31:0] EX_pc;
  logic [19:15] EX_src_reg_1;
  logic [24:20] EX_src_reg_2;
  logic [11:7] EX_dest_reg;
  logic [31:0] EX_imm_ext;
  logic [31:0] EX_pc_plus_4;
  logic [31:0] EX_src_a_tick;
  logic [31:0] EX_src_a;
  logic [31:0] EX_src_b;
  logic [31:0] EX_pc_target_src_a;
  logic [31:0] EX_wr_data;
  logic [31:0] EX_alu_result;
  logic [31:0] EX_pc_target;

  // data memory signals
  logic MEM_reg_wr;
  logic [1:0] MEM_result_src;
  logic [2:0] MEM_load_size;
  logic [11:7] MEM_dest_reg;
  logic [31:0] MEM_pc_plus_4;
  logic [31:0] MEM_rd_data;
  logic [1:0] MEM_mem_wr_size;
  logic [31:0] MEM_wr_data;
  logic [31:0] MEM_alu_result;
  // write back signals
  logic WB_reg_wr;
  logic [1:0] WB_result_src;
  logic [31:0] WB_alu_result;
  logic [31:0] WB_rd_data;
  logic [11:7] WB_dest_reg;
  logic [31:0] WB_pc_plus_4;
  logic [31:0] WB_result;


  // hazard unit signals
  logic IF_stall;
  logic ID_stall;
  logic ID_flush;
  logic EX_flush;
  logic [1:0] EX_forward_a;
  logic [1:0] EX_forward_b;

  // DMEM interface
  assign DMEM_wr_data_o = DMEM_wr_data;
  assign DMEM_wr_byte_en_o = DMEM_wr_byte_en;

  // IMEM interface
  assign IMEM_addr_o = IMEM_addr;
  assign DMEM_addr_o = DMEM_addr;

  // Instruction Fetch stage
  dtcore32_IF_stage  dtcore32_IF_stage_inst (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .IF_stall_n_i(IF_stall_n_i),
    .EX_pc_target_i(EX_pc_target_i),
    .EX_pc_src_i(EX_pc_src_i),
    .IF_pc_plus_4_o(IF_pc_plus_4_o),
    .IMEM_addr_o(IMEM_addr_o)
  );

  dtcore32_IF_ID_reg  dtcore32_IF_ID_reg_inst (
                        .clk_i(clk_i),
                        .rst_i(rst_i),
                        .ID_flush_i(ID_flush_i),
                        .ID_stall_i(ID_stall_i),
                        .IMEM_rd_data_i(IMEM_rd_data_i),
                        .IMEM_addr_i(IMEM_addr_i),
                        .IF_pc_plus_4_i(IF_pc_plus_4_i),
                        .ID_instr_o(ID_instr_o),
                        .ID_pc_o(ID_pc_o),
                        .ID_pc_plus_4_o(ID_pc_plus_4_o)
                      );


  //Instruction Decode stage
                      dtcore32_ID_stage  dtcore32_ID_stage_inst (
                        .ID_instr_i(ID_instr_i),
                        .ID_pc_i(ID_pc_i),
                        .WB_reg_wr_en_i(WB_reg_wr_en_i),
                        .WB_csr_wr_en_i(WB_csr_wr_en_i),
                        .WB_dest_reg_i(WB_dest_reg_i),
                        .WB_result_i(WB_result_i),
                        .WB_csr_wr_data_i(WB_csr_wr_data_i),
                        .ID_reg_wr_en_o(ID_reg_wr_en_o),
                        .ID_result_src_o(ID_result_src_o),
                        .ID_load_size_o(ID_load_size_o),
                        .ID_mem_wr_size_o(ID_mem_wr_size_o),
                        .ID_jump_o(ID_jump_o),
                        .ID_branch_o(ID_branch_o),
                        .ID_alu_control_o(ID_alu_control_o),
                        .ID_alu_b_src_o(ID_alu_b_src_o),
                        .ID_alu_a_src_o(ID_alu_a_src_o),
                        .ID_pc_target_alu_src_o(ID_pc_target_alu_src_o),
                        .ID_csr_wr_en_o(ID_csr_wr_en_o),
                        .ID_reg_data_1_o(ID_reg_data_1_o),
                        .ID_reg_data_2_o(ID_reg_data_2_o),
                        .ID_pc_o(ID_pc_o),
                        .ID_src_reg_1_o(ID_src_reg_1_o),
                        .ID_src_reg_2_o(ID_src_reg_2_o),
                        .ID_dest_reg_o(ID_dest_reg_o),
                        .ID_imm_ext_o(ID_imm_ext_o),
                        .ID_csr_rd_data_o(ID_csr_rd_data_o),
                        .ID_exception_o(ID_exception_o)
                      );

  // ID/EX register
  dtcore32_ID_EX_reg  dtcore32_ID_EX_reg_inst (
                        .clk_i(clk_i),
                        .rst_i(rst_i),
                        .EX_flush_i(EX_flush_i),
                        .ID_reg_wr_en_i(ID_reg_wr_en_i),
                        .ID_result_src_i(ID_result_src_i),
                        .ID_load_size_i(ID_load_size_i),
                        .ID_mem_wr_size_i(ID_mem_wr_size_i),
                        .ID_jump_i(ID_jump_i),
                        .ID_branch_i(ID_branch_i),
                        .ID_alu_control_i(ID_alu_control_i),
                        .ID_alu_b_src_i(ID_alu_b_src_i),
                        .ID_alu_a_src_i(ID_alu_a_src_i),
                        .ID_pc_target_alu_src_i(ID_pc_target_alu_src_i),
                        .ID_csr_wr_en_i(ID_csr_wr_en_i),
                        .ID_reg_data_1_i(ID_reg_data_1_i),
                        .ID_reg_data_2_i(ID_reg_data_2_i),
                        .ID_pc_i(ID_pc_i),
                        .ID_src_reg_1_i(ID_src_reg_1_i),
                        .ID_src_reg_2_i(ID_src_reg_2_i),
                        .ID_dest_reg_i(ID_dest_reg_i),
                        .ID_imm_ext_i(ID_imm_ext_i),
                        .ID_pc_plus_4_i(ID_pc_plus_4_i),
                        .ID_csr_rd_data_i(ID_csr_rd_data_i),
                        .EX_reg_wr_en_o(EX_reg_wr_en_o),
                        .EX_result_src_o(EX_result_src_o),
                        .EX_load_size_o(EX_load_size_o),
                        .EX_mem_wr_size_o(EX_mem_wr_size_o),
                        .EX_jump_o(EX_jump_o),
                        .EX_branch_o(EX_branch_o),
                        .EX_alu_control_o(EX_alu_control_o),
                        .EX_alu_b_src_o(EX_alu_b_src_o),
                        .EX_alu_a_src_o(EX_alu_a_src_o),
                        .EX_pc_target_alu_src_o(EX_pc_target_alu_src_o),
                        .EX_csr_wr_en_o(EX_csr_wr_en_o),
                        .EX_reg_data_1_o(EX_reg_data_1_o),
                        .EX_reg_data_2_o(EX_reg_data_2_o),
                        .EX_pc_o(EX_pc_o),
                        .EX_src_reg_1_o(EX_src_reg_1_o),
                        .EX_src_reg_2_o(EX_src_reg_2_o),
                        .EX_dest_reg_o(EX_dest_reg_o),
                        .EX_imm_ext_o(EX_imm_ext_o),
                        .EX_pc_plus_4_o(EX_pc_plus_4_o),
                        .EX_csr_rd_data_o(EX_csr_rd_data_o)
                      );

  // Instruction Execute stage
  dtcore32_EX_stage  dtcore32_EX_stage_inst (
                       .EX_jump_i(EX_jump_i),
                       .EX_branch_i(EX_branch_i),
                       .EX_alu_control_i(EX_alu_control_i),
                       .EX_alu_b_src_i(EX_alu_b_src_i),
                       .EX_alu_a_src_i(EX_alu_a_src_i),
                       .EX_pc_target_alu_src_i(EX_pc_target_alu_src_i),
                       .EX_reg_data_1_i(EX_reg_data_1_i),
                       .EX_reg_data_2_i(EX_reg_data_2_i),
                       .EX_pc_i(EX_pc_i),
                       .EX_imm_ext_i(EX_imm_ext_i),
                       .EX_forward_a_i(EX_forward_a_i),
                       .EX_forward_b_i(EX_forward_b_i),
                       .EX_csr_rd_data_i(EX_csr_rd_data_i),
                       .MEM_alu_result_i(MEM_alu_result_i),
                       .WB_result_i(WB_result_i),
                       .EX_pc_src_o(EX_pc_src_o),
                       .EX_alu_result_o(EX_alu_result_o),
                       .EX_dmem_wr_data_o(EX_dmem_wr_data_o),
                       .EX_pc_target_o(EX_pc_target_o)
                     );
  // EX/MEM register
  dtcore32_EX_MEM_reg  dtcore32_EX_MEM_reg_inst (
                         .clk_i(clk_i),
                         .rst_i(rst_i),
                         .EX_reg_wr_en_i(EX_reg_wr_en_i),
                         .EX_result_src_i(EX_result_src_i),
                         .EX_load_size_i(EX_load_size_i),
                         .EX_mem_wr_size_i(EX_mem_wr_size_i),
                         .EX_csr_wr_en_i(EX_csr_wr_en_i),
                         .EX_alu_result_i(EX_alu_result_i),
                         .EX_wr_data_i(EX_wr_data_i),
                         .EX_dest_reg_i(EX_dest_reg_i),
                         .EX_pc_plus_4_i(EX_pc_plus_4_i),
                         .EX_csr_rd_data_i(EX_csr_rd_data_i),
                         .MEM_reg_wr_en_o(MEM_reg_wr_en_o),
                         .MEM_result_src_o(MEM_result_src_o),
                         .MEM_load_size_o(MEM_load_size_o),
                         .MEM_mem_wr_size_o(MEM_mem_wr_size_o),
                         .MEM_csr_wr_en_o(MEM_csr_wr_en_o),
                         .MEM_alu_result_o(MEM_alu_result_o),
                         .MEM_wr_data_o(MEM_wr_data_o),
                         .MEM_dest_reg_o(MEM_dest_reg_o),
                         .MEM_pc_plus_4_o(MEM_pc_plus_4_o),
                         .MEM_csr_rd_data_o(MEM_csr_rd_data_o)
                       );


  // Data Memory stage
  dtcore32_MEM_stage  dtcore32_MEM_stage_inst (
                        .MEM_load_size_i(MEM_load_size_i),
                        .MEM_mem_wr_size_i(MEM_mem_wr_size_i),
                        .MEM_alu_result_i(MEM_alu_result_i),
                        .MEM_dmem_wr_data_i(MEM_dmem_wr_data_i),
                        .DMEM_rd_data_i(DMEM_rd_data_i),
                        .MEM_dmem_rd_data_o(MEM_dmem_rd_data_o),
                        .DMEM_wr_byte_en_o(DMEM_wr_byte_en_o),
                        .DMEM_wr_data_o(DMEM_wr_data_o),
                        .MEM_misaligned_store_o(MEM_misaligned_store_o),
                        .MEM_misaligned_load_o(MEM_misaligned_load_o),
                        .MEM_unknown_load_o(MEM_unknown_load_o)
                      );


  dtcore32_MEM_WB_reg  dtcore32_MEM_WB_reg_inst (
                         .clk_i(clk_i),
                         .rst_i(rst_i),
                         .MEM_reg_wr_en_i(MEM_reg_wr_en_i),
                         .MEM_result_src_i(MEM_result_src_i),
                         .MEM_csr_wr_en_i(MEM_csr_wr_en_i),
                         .MEM_alu_result_i(MEM_alu_result_i),
                         .MEM_dmem_rd_data_i(MEM_dmem_rd_data_i),
                         .MEM_dest_reg_i(MEM_dest_reg_i),
                         .MEM_pc_plus_4_i(MEM_pc_plus_4_i),
                         .MEM_csr_rd_data_i(MEM_csr_rd_data_i),
                         .WB_reg_wr_en_o(WB_reg_wr_en_o),
                         .WB_result_src_o(WB_result_src_o),
                         .WB_csr_wr_en_o(WB_csr_wr_en_o),
                         .WB_alu_result_o(WB_alu_result_o),
                         .WB_dmem_rd_data_o(WB_dmem_rd_data_o),
                         .WB_dest_reg_o(WB_dest_reg_o),
                         .WB_pc_plus_4_o(WB_pc_plus_4_o),
                         .WB_csr_rd_data_o(WB_csr_rd_data_o)
                       );


  dtcore32_WB_stage  dtcore32_WB_stage_inst (
                       .WB_result_src_i(WB_result_src_i),
                       .WB_alu_result_i(WB_alu_result_i),
                       .WB_dmem_rd_data_i(WB_dmem_rd_data_i),
                       .WB_pc_plus_4_i(WB_pc_plus_4_i),
                       .WB_csr_rd_data_i(WB_csr_rd_data_i),
                       .WB_result_o(WB_result_o)
                     );

  // Hazard Unit
  dtcore32_hazunit  dtcore32_hazunit_inst (
                      .Rs1E(EX_src_reg_1),
                      .Rs2E(EX_src_reg_2),
                      .RdM(MEM_dest_reg),
                      .RdW(WB_dest_reg),
                      .RegWriteM(MEM_reg_wr),
                      .RegWriteW(WB_reg_wr),
                      .ResultSrcEb0(EX_result_src[0]),
                      .Rs1D(ID_src_reg_1),
                      .Rs2D(ID_src_reg_2),
                      .RdE(EX_dest_reg),
                      .PCSrcE(EX_pc_src),
                      .ForwardAE(EX_forward_a),
                      .ForwardBE(EX_forward_b),
                      .StallF(IF_stall),
                      .StallD(ID_stall),
                      .FlushE(EX_flush),
                      .FlushD(ID_flush)
                    );
endmodule
