`include "formal_defs.svh"
import riscv_pkg::*;
module id_ex_pipeline (
  input  logic        clk_i               ,
  input  logic        rst_i               ,
  input  logic        id_ex_flush         ,
  input  logic        id_ex_stall         ,
  input  logic        if_id_stall         ,
  input  logic        id_d_valid          ,
  input  logic [31:0] id_d_pc             ,
  input  logic [31:0] id_d_pc_plus_4      ,
  input  logic [ 4:0] id_d_rs1_addr       ,
  input  logic [ 4:0] id_d_rs2_addr       ,
  input  logic [ 4:0] id_d_rd_addr        ,
  input  logic [31:0] id_d_rs1_rdata      ,
  input  logic [31:0] id_d_rs2_rdata      ,
  input  logic [31:0] id_d_imm_ext        ,
  input  logic [11:0] id_d_csr_addr       ,
  input  logic [31:0] id_d_csr_rdata      ,
  input  logic [ 3:0] id_d_alu_control    ,
  input  logic [ 1:0] id_d_alu_a_sel      ,
  input  logic        id_d_alu_b_sel      ,
  input  logic        id_d_pc_alu_sel     ,
  input  logic  id_d_csr_bitmask_sel,
  input  logic        id_d_is_branch      ,
  input  logic        id_d_is_jump        ,
  input  logic        id_d_is_csr_write   ,
  input  logic        id_d_is_csr_read    ,
  input  logic        id_d_is_rd_write    ,
  input  logic        id_d_is_rs1_read    ,
  input  logic        id_d_is_rs2_read    ,
  input  logic        id_d_is_mem_write   ,
  input  logic        id_d_is_mem_read    ,
  input  logic        id_d_is_jal         ,
  input  logic        id_d_is_jalr        ,
  input  logic        id_d_is_memsize_b   ,
  input  logic        id_d_is_memsize_bu  ,
  input  logic        id_d_is_memsize_h   ,
  input  logic        id_d_is_memsize_hu  ,
  input  logic        id_d_is_memsize_w   ,
  input  logic        id_d_csr_op_rw      ,
  input  logic        id_d_csr_op_clear   ,
  input  logic        id_d_csr_op_set     ,
  input  logic        id_d_branch_predict ,
  input  logic [ 5:0] id_d_pht_idx        ,
  input  logic        id_d_trap_valid     ,
  input  logic [31:0] id_d_trap_mcause    ,
  input  logic [31:0] id_d_trap_pc        ,
`ifdef RISCV_FORMAL
  input  logic [31:0] id_d_insn           ,
  input  logic        id_d_intr           ,
  input  logic [31:0] id_d_trap_insn      ,
  input  logic [31:0] id_d_trap_next_pc   ,
  input  logic [ 4:0] id_d_trap_rs1_addr  ,
  input  logic [ 4:0] id_d_trap_rs2_addr  ,
  input  logic [ 4:0] id_d_trap_rd_addr   ,
  input  logic [31:0] id_d_trap_rs1_rdata ,
  input  logic [31:0] id_d_trap_rs2_rdata ,
  input  logic [31:0] id_d_trap_rd_wdata  ,
  output logic [31:0] ex_q_insn           ,
  output logic        ex_q_intr           ,
  output logic [31:0] ex_q_trap_insn      ,
  output logic [31:0] ex_q_trap_next_pc   ,
  output logic [ 4:0] ex_q_trap_rs1_addr  ,
  output logic [ 4:0] ex_q_trap_rs2_addr  ,
  output logic [ 4:0] ex_q_trap_rd_addr   ,
  output logic [31:0] ex_q_trap_rs1_rdata ,
  output logic [31:0] ex_q_trap_rs2_rdata ,
  output logic [31:0] ex_q_trap_rd_wdata  ,
`endif
  output logic        ex_q_valid          ,
  output logic [31:0] ex_q_pc             ,
  output logic [31:0] ex_q_pc_plus_4      ,
  output logic [ 4:0] ex_q_rs1_addr       ,
  output logic [ 4:0] ex_q_rs2_addr       ,
  output logic [ 4:0] ex_q_rd_addr        ,
  output logic [31:0] ex_q_rs1_rdata      ,
  output logic [31:0] ex_q_rs2_rdata      ,
  output logic [31:0] ex_q_imm_ext        ,
  output logic [11:0] ex_q_csr_addr       ,
  output logic [31:0] ex_q_csr_rdata      ,
  output logic [ 3:0] ex_q_alu_control    ,
  output logic [ 1:0] ex_q_alu_a_sel      ,
  output logic        ex_q_alu_b_sel      ,
  output logic        ex_q_pc_alu_sel     ,
  output logic        ex_q_csr_bitmask_sel,
  output logic        ex_q_is_branch      ,
  output logic        ex_q_is_jump        ,
  output logic        ex_q_is_csr_write   ,
  output logic        ex_q_is_csr_read    ,
  output logic        ex_q_is_rd_write    ,
  output logic        ex_q_is_rs1_read    ,
  output logic        ex_q_is_rs2_read    ,
  output logic        ex_q_is_mem_write   ,
  output logic        ex_q_is_mem_read    ,
  output logic        ex_q_is_jal         ,
  output logic        ex_q_is_jalr        ,
  output logic        ex_q_is_memsize_b   ,
  output logic        ex_q_is_memsize_bu  ,
  output logic        ex_q_is_memsize_h   ,
  output logic        ex_q_is_memsize_hu  ,
  output logic        ex_q_is_memsize_w   ,
  output logic        ex_q_csr_op_rw      ,
  output logic        ex_q_csr_op_clear   ,
  output logic        ex_q_csr_op_set     ,
  output logic        ex_q_branch_predict ,
  output logic [ 5:0] ex_q_pht_idx        ,
  output logic        ex_q_trap_valid     ,
  output logic [31:0] ex_q_trap_mcause    ,
  output logic [31:0] ex_q_trap_pc
);

  always_ff @(posedge clk_i) begin
    // clear the pipeline on reset, flush,
    // or imem buffer invalid AND the stage is not stalled
    if (rst_i || id_ex_flush || (!id_ex_stall && if_id_stall)) begin
      // clear all EX stage registers
      ex_q_valid     <= 0;
      ex_q_pc        <= 0;
      ex_q_pc_plus_4 <= 0;
      ex_q_rs1_addr  <= 0;
      ex_q_rs2_addr  <= 0;
      ex_q_rd_addr   <= 0;
      ex_q_rs1_rdata <= 0;
      ex_q_rs2_rdata <= 0;
      ex_q_imm_ext   <= 0;
      ex_q_csr_addr  <= 0;
      ex_q_csr_rdata <= 0;

      ex_q_alu_control     <= 0;
      ex_q_alu_a_sel       <= 0;
      ex_q_alu_b_sel       <= 0;
      ex_q_pc_alu_sel      <= 0;
      ex_q_csr_bitmask_sel <= 0;

      ex_q_is_branch    <= 0;
      ex_q_is_jump      <= 0;
      ex_q_is_csr_write <= 0;
      ex_q_is_csr_read  <= 0;
      ex_q_is_rd_write  <= 0;
      ex_q_is_rs1_read  <= 0;
      ex_q_is_rs2_read  <= 0;
      ex_q_is_mem_write <= 0;
      ex_q_is_mem_read  <= 0;

      ex_q_is_jal        <= 0;
      ex_q_is_jalr       <= 0;
      ex_q_is_memsize_b  <= 0;
      ex_q_is_memsize_bu <= 0;
      ex_q_is_memsize_h  <= 0;
      ex_q_is_memsize_hu <= 0;
      ex_q_is_memsize_w  <= 0;

      ex_q_csr_op_rw    <= 0;
      ex_q_csr_op_clear <= 0;
      ex_q_csr_op_set   <= 0;

      ex_q_branch_predict <= 0;
      ex_q_pht_idx        <= 0;

      ex_q_trap_valid  <= 0;
      ex_q_trap_mcause <= 0;
      ex_q_trap_pc     <= 0;

`ifdef RISCV_FORMAL
      ex_q_insn <= 0;
      ex_q_intr <= 0;

      ex_q_trap_insn      <= 0;
      ex_q_trap_next_pc   <= 0;
      ex_q_trap_rs1_addr  <= 0;
      ex_q_trap_rs2_addr  <= 0;
      ex_q_trap_rd_addr   <= 0;
      ex_q_trap_rs1_rdata <= 0;
      ex_q_trap_rs2_rdata <= 0;
      ex_q_trap_rd_wdata  <= 0;
`endif

    end else if (!if_id_stall) begin
      // propagate ID stage values to EX stage
      ex_q_valid     <= id_d_valid;
      ex_q_pc        <= id_d_pc;
      ex_q_pc_plus_4 <= id_d_pc_plus_4;
      ex_q_rs1_addr  <= id_d_rs1_addr;
      ex_q_rs2_addr  <= id_d_rs2_addr;
      ex_q_rd_addr   <= id_d_rd_addr;
      ex_q_rs1_rdata <= id_d_rs1_rdata;
      ex_q_rs2_rdata <= id_d_rs2_rdata;
      ex_q_imm_ext   <= id_d_imm_ext;
      ex_q_csr_addr  <= id_d_csr_addr;
      ex_q_csr_rdata <= id_d_csr_rdata;

      ex_q_alu_control     <= id_d_alu_control;
      ex_q_alu_a_sel       <= id_d_alu_a_sel;
      ex_q_alu_b_sel       <= id_d_alu_b_sel;
      ex_q_pc_alu_sel      <= id_d_pc_alu_sel;
      ex_q_csr_bitmask_sel <= id_d_csr_bitmask_sel;

      ex_q_is_branch    <= id_d_is_branch;
      ex_q_is_jump      <= id_d_is_jump;
      ex_q_is_csr_write <= id_d_is_csr_write;
      ex_q_is_csr_read  <= id_d_is_csr_read;
      ex_q_is_rd_write  <= id_d_is_rd_write;
      ex_q_is_rs1_read  <= id_d_is_rs1_read;
      ex_q_is_rs2_read  <= id_d_is_rs2_read;
      ex_q_is_mem_write <= id_d_is_mem_write;
      ex_q_is_mem_read  <= id_d_is_mem_read;

      ex_q_is_jal        <= id_d_is_jal;
      ex_q_is_jalr       <= id_d_is_jalr;
      ex_q_is_memsize_b  <= id_d_is_memsize_b;
      ex_q_is_memsize_bu <= id_d_is_memsize_bu;
      ex_q_is_memsize_h  <= id_d_is_memsize_h;
      ex_q_is_memsize_hu <= id_d_is_memsize_hu;
      ex_q_is_memsize_w  <= id_d_is_memsize_w;

      ex_q_csr_op_rw    <= id_d_csr_op_rw;
      ex_q_csr_op_clear <= id_d_csr_op_clear;
      ex_q_csr_op_set   <= id_d_csr_op_set;

      ex_q_branch_predict <= id_d_branch_predict;
      ex_q_pht_idx        <= id_d_pht_idx;

      ex_q_trap_valid  <= id_d_trap_valid;
      ex_q_trap_mcause <= id_d_trap_mcause;
      ex_q_trap_pc     <= id_d_trap_pc;

`ifdef RISCV_FORMAL
      ex_q_insn <= id_d_insn;
      ex_q_intr <= id_d_intr;

      ex_q_trap_insn      <= id_d_trap_insn;
      ex_q_trap_next_pc   <= id_d_trap_next_pc;
      ex_q_trap_rs1_addr  <= id_d_trap_rs1_addr;
      ex_q_trap_rs2_addr  <= id_d_trap_rs2_addr;
      ex_q_trap_rd_addr   <= id_d_trap_rd_addr;
      ex_q_trap_rs1_rdata <= id_d_trap_rs1_rdata;
      ex_q_trap_rs2_rdata <= id_d_trap_rs2_rdata;
      ex_q_trap_rd_wdata  <= id_d_trap_rd_wdata;
`endif
    end
  end

endmodule
