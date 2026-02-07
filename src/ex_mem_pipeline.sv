`include "formal_defs.svh"
import riscv_pkg::*;
module ex_mem_pipeline (
  input  logic       clk_i,
  input  logic       rst_i,
  input  logic       ex_mem_flush,
  input  logic       ex_mem_stall,
  input  logic       id_ex_stall,
  input  logic       ex_d_valid,
  input  logic [31:0] ex_d_pc,
  input  logic [31:0] ex_d_pc_plus_4,
  input  logic [4:0]  ex_d_rd_addr,
  input  logic [11:0] ex_d_csr_addr,
  input  logic [31:0] ex_d_csr_wdata,
  input  logic [31:0] ex_d_store_wdata,
  input  logic [31:0] ex_d_alu_csr_result,
  input  logic        ex_d_is_branch,
  input  logic        ex_d_is_jump,
  input  logic        ex_d_is_csr_write,
  input  logic        ex_d_is_csr_read,
  input  logic        ex_d_is_rd_write,
  input  logic        ex_d_is_mem_write,
  input  logic        ex_d_is_mem_read,
  input  logic        ex_d_is_jal,
  input  logic        ex_d_is_jalr,
  input  logic        ex_d_is_memsize_b,
  input  logic        ex_d_is_memsize_bu,
  input  logic        ex_d_is_memsize_h,
  input  logic        ex_d_is_memsize_hu,
  input  logic        ex_d_is_memsize_w,
  input  logic        ex_d_branch_predict,
  input  logic [5:0]  ex_d_pht_idx,
  input  logic        ex_d_jump_taken,
  input  logic [31:0] ex_d_jaddr,
  input  logic        ex_d_trap_valid,
  input  logic [31:0] ex_d_trap_mcause,
  input  logic [31:0] ex_d_trap_pc,
`ifdef RISCV_FORMAL
  input  logic [31:0] ex_d_insn,
  input  logic        ex_d_intr,
  input  logic [31:0] ex_d_next_pc,
  input  logic [31:0] ex_d_csr_rdata,
  input  logic [4:0]  ex_d_rs1_addr,
  input  logic [4:0]  ex_d_rs2_addr,
  input  logic [31:0] ex_d_rs1_rdata,
  input  logic [31:0] ex_d_rs2_rdata,
  input  logic [31:0] ex_d_trap_insn,
  input  logic [31:0] ex_d_trap_next_pc,
  input  logic [4:0]  ex_d_trap_rs1_addr,
  input  logic [4:0]  ex_d_trap_rs2_addr,
  input  logic [4:0]  ex_d_trap_rd_addr,
  input  logic [31:0] ex_d_trap_rs1_rdata,
  input  logic [31:0] ex_d_trap_rs2_rdata,
  input  logic [31:0] ex_d_trap_rd_wdata,
  output logic [31:0] mem_q_insn,
  output logic        mem_q_intr,
  output logic [31:0] mem_q_next_pc,
  output logic [31:0] mem_q_csr_rdata,
  output logic [4:0]  mem_q_rs1_addr,
  output logic [4:0]  mem_q_rs2_addr,
  output logic [31:0] mem_q_rs1_rdata,
  output logic [31:0] mem_q_rs2_rdata,
  output logic [31:0] mem_q_trap_insn,
  output logic [31:0] mem_q_trap_next_pc,
  output logic [4:0]  mem_q_trap_rs1_addr,
  output logic [4:0]  mem_q_trap_rs2_addr,
  output logic [4:0]  mem_q_trap_rd_addr,
  output logic [31:0] mem_q_trap_rs1_rdata,
  output logic [31:0] mem_q_trap_rs2_rdata,
  output logic [31:0] mem_q_trap_rd_wdata,
`endif
  output logic       mem_q_valid,
  output logic [31:0] mem_q_pc,
  output logic [31:0] mem_q_pc_plus_4,
  output logic [4:0]  mem_q_rd_addr,
  output logic [11:0] mem_q_csr_addr,
  output logic [31:0] mem_q_csr_wdata,
  output logic [31:0] mem_q_store_wdata,
  output logic [31:0] mem_q_alu_csr_result,
  output logic        mem_q_is_branch,
  output logic        mem_q_is_jump,
  output logic        mem_q_is_csr_write,
  output logic        mem_q_is_csr_read,
  output logic        mem_q_is_rd_write,
  output logic        mem_q_is_mem_write,
  output logic        mem_q_is_mem_read,
  output logic        mem_q_is_jal,
  output logic        mem_q_is_jalr,
  output logic        mem_q_is_memsize_b,
  output logic        mem_q_is_memsize_bu,
  output logic        mem_q_is_memsize_h,
  output logic        mem_q_is_memsize_hu,
  output logic        mem_q_is_memsize_w,
  output logic        mem_q_branch_predict,
  output logic [5:0]  mem_q_pht_idx,
  output logic        mem_q_jump_taken,
  output logic [31:0] mem_q_jaddr,
  output logic        mem_q_trap_valid,
  output logic [31:0] mem_q_trap_mcause,
  output logic [31:0] mem_q_trap_pc
);

always_ff @(posedge clk_i) begin
    if (rst_i || ex_mem_flush || (!ex_mem_stall && id_ex_stall)) begin
      // clear EX/MEM pipeline registers
      mem_q_valid          <= 0;
      mem_q_pc             <= 0;
      mem_q_pc_plus_4      <= 0;
      mem_q_rd_addr        <= 0;
      mem_q_csr_addr       <= 0;
      mem_q_csr_wdata      <= 0;
      mem_q_store_wdata    <= 0;
      mem_q_alu_csr_result <= 0;

      mem_q_is_branch    <= 0;
      mem_q_is_jump      <= 0;
      mem_q_is_csr_write <= 0;
      mem_q_is_csr_read  <= 0;
      mem_q_is_rd_write  <= 0;
      mem_q_is_mem_write <= 0;
      mem_q_is_mem_read  <= 0;

      mem_q_is_jal        <= 0;
      mem_q_is_jalr       <= 0;
      mem_q_is_memsize_b  <= 0;
      mem_q_is_memsize_bu <= 0;
      mem_q_is_memsize_h  <= 0;
      mem_q_is_memsize_hu <= 0;
      mem_q_is_memsize_w  <= 0;

      mem_q_branch_predict <= 0;
      mem_q_pht_idx        <= 0;

      mem_q_jump_taken <= 0;
      mem_q_jaddr      <= 0;

      mem_q_trap_valid  <= 0;
      mem_q_trap_mcause <= 0;
      mem_q_trap_pc     <= 0;

`ifdef RISCV_FORMAL
      mem_q_insn           <= 0;
      mem_q_intr           <= 0;
      mem_q_next_pc        <= 0;
      mem_q_csr_rdata      <= 0;
      mem_q_rs1_addr       <= 0;
      mem_q_rs2_addr       <= 0;
      mem_q_rs1_rdata      <= 0;
      mem_q_rs2_rdata      <= 0;
      mem_q_trap_insn      <= 0;
      mem_q_trap_next_pc   <= 0;
      mem_q_trap_rs1_addr  <= 0;
      mem_q_trap_rs2_addr  <= 0;
      mem_q_trap_rd_addr   <= 0;
      mem_q_trap_rs1_rdata <= 0;
      mem_q_trap_rs2_rdata <= 0;
      mem_q_trap_rd_wdata  <= 0;
`endif
    end else if (!ex_mem_stall) begin
      // propagate EX stage outputs to MEM stage
      mem_q_valid          <= ex_d_valid;
      mem_q_pc             <= ex_d_pc;
      mem_q_pc_plus_4      <= ex_d_pc_plus_4;
      mem_q_rd_addr        <= ex_d_rd_addr;
      mem_q_csr_addr       <= ex_d_csr_addr;
      mem_q_csr_wdata      <= ex_d_csr_wdata;
      mem_q_store_wdata    <= ex_d_store_wdata;
      mem_q_alu_csr_result <= ex_d_alu_csr_result;

      mem_q_is_branch    <= ex_d_is_branch;
      mem_q_is_jump      <= ex_d_is_jump;
      mem_q_is_csr_write <= ex_d_is_csr_write;
      mem_q_is_csr_read  <= ex_d_is_csr_read;
      mem_q_is_rd_write  <= ex_d_is_rd_write;
      mem_q_is_mem_write <= ex_d_is_mem_write;
      mem_q_is_mem_read  <= ex_d_is_mem_read;

      mem_q_is_jal        <= ex_d_is_jal;
      mem_q_is_jalr       <= ex_d_is_jalr;
      mem_q_is_memsize_b  <= ex_d_is_memsize_b;
      mem_q_is_memsize_bu <= ex_d_is_memsize_bu;
      mem_q_is_memsize_h  <= ex_d_is_memsize_h;
      mem_q_is_memsize_hu <= ex_d_is_memsize_hu;
      mem_q_is_memsize_w  <= ex_d_is_memsize_w;

      mem_q_branch_predict <= ex_d_branch_predict;
      mem_q_pht_idx        <= ex_d_pht_idx;

      mem_q_jump_taken <= ex_d_jump_taken;
      mem_q_jaddr      <= ex_d_jaddr;

      mem_q_trap_valid  <= ex_d_trap_valid;
      mem_q_trap_mcause <= ex_d_trap_mcause;
      mem_q_trap_pc     <= ex_d_trap_pc;

`ifdef RISCV_FORMAL
      mem_q_insn           <= ex_d_insn;
      mem_q_intr           <= ex_d_intr;
      mem_q_next_pc        <= ex_d_next_pc;
      mem_q_csr_rdata      <= ex_d_csr_rdata;
      mem_q_rs1_addr       <= ex_d_rs1_addr;
      mem_q_rs2_addr       <= ex_d_rs2_addr;
      mem_q_rs1_rdata      <= ex_d_rs1_rdata;
      mem_q_rs2_rdata      <= ex_d_rs2_rdata;
      mem_q_trap_insn      <= ex_d_trap_insn;
      mem_q_trap_next_pc   <= ex_d_trap_next_pc;
      mem_q_trap_rs1_addr  <= ex_d_trap_rs1_addr;
      mem_q_trap_rs2_addr  <= ex_d_trap_rs2_addr;
      mem_q_trap_rd_addr   <= ex_d_trap_rd_addr;
      mem_q_trap_rs1_rdata <= ex_d_trap_rs1_rdata;
      mem_q_trap_rs2_rdata <= ex_d_trap_rs2_rdata;
      mem_q_trap_rd_wdata  <= ex_d_trap_rd_wdata;
`endif
    end
  end
  
endmodule
