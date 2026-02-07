//===========================================================
// Project    : RISC-V CPU
// File       : dtcore32.v
// Module     : dtcore32
// Description: Top-level CPU core module implementing a 32-bit
//              RISC-V pipeline. Interfaces with instruction memory,
//              and a unified data interface for memory-mapped
//              data memory or peripherals. Handles CSR, traps, and
//              optional formal verification signals (`RISCV_FORMAL`).
//
// Inputs:
//   clk_i                - System clock
//   rst_i                - Synchronous reset
//   imem_rdata_i         - Instruction memory read data
//   mem_rdata_i          - Read data from data memory or peripheral
//   mem_done_i           - Transaction completion from data memory or peripheral
//   (RISCV_FORMAL) rvfi signals - Optional outputs for formal verification
//
// Outputs:
//   imem_addr_o          - Instruction memory address
//   mem_valid_o          - Valid signal for data memory or peripheral transaction
//   mem_wen_o            - Write enable for data memory or peripheral
//   mem_addr_o           - Address for data memory or peripheral
//   mem_wdata_o          - Write data for data memory or peripheral
//   mem_strb_o           - Byte-enable strobes for write operations
//   (RISCV_FORMAL) rvfi signals - Optional formal verification outputs
//
// Notes:
//   - Integrates instruction fetch, decode, execute, memory, and write-back stages.
//   - Unified `mem_*` interface can access both data memory and memory-mapped peripherals.
//   - Optional RISCV_FORMAL signals allow formal verification of CPU behavior.
//   - Designed to interface with external CSR module and trap handling logic.
//
// Author     : David Torres
// Date       : 2025-09-16
//===========================================================
`include "formal_defs.svh"
import riscv_pkg::*;
module dtcore32 (
  input               clk_i                  ,
  input               rst_i                  ,
`ifdef RISCV_FORMAL
  output logic        rvfi_valid             ,
  output logic [63:0] rvfi_order             ,
  output logic [31:0] rvfi_insn              ,
  output logic        rvfi_trap              ,
  output logic        rvfi_halt              ,
  output logic        rvfi_intr              ,
  output logic [ 1:0] rvfi_mode              ,
  output logic [ 1:0] rvfi_ixl               ,
  output logic [ 4:0] rvfi_rs1_addr          ,
  output logic [ 4:0] rvfi_rs2_addr          ,
  output logic [31:0] rvfi_rs1_rdata         ,
  output logic [31:0] rvfi_rs2_rdata         ,
  output logic [ 4:0] rvfi_rd_addr           ,
  output logic [31:0] rvfi_rd_wdata          ,
  output logic [31:0] rvfi_pc_rdata          ,
  output logic [31:0] rvfi_pc_wdata          ,
  output logic [31:0] rvfi_mem_addr          ,
  output logic [ 3:0] rvfi_mem_rmask         ,
  output logic [ 3:0] rvfi_mem_wmask         ,
  output logic [31:0] rvfi_mem_rdata         ,
  output logic [31:0] rvfi_mem_wdata         ,
  output logic [63:0] rvfi_csr_mcycle_rmask  ,
  output logic [63:0] rvfi_csr_mcycle_wmask  ,
  output logic [63:0] rvfi_csr_mcycle_rdata  ,
  output logic [63:0] rvfi_csr_mcycle_wdata  ,
  output logic [63:0] rvfi_csr_minstret_rmask,
  output logic [63:0] rvfi_csr_minstret_wmask,
  output logic [63:0] rvfi_csr_minstret_rdata,
  output logic [63:0] rvfi_csr_minstret_wdata,
  output logic [31:0] rvfi_csr_mcause_rmask  ,
  output logic [31:0] rvfi_csr_mcause_wmask  ,
  output logic [31:0] rvfi_csr_mcause_rdata  ,
  output logic [31:0] rvfi_csr_mcause_wdata  ,
  output logic [31:0] rvfi_csr_mepc_rmask    ,
  output logic [31:0] rvfi_csr_mepc_wmask    ,
  output logic [31:0] rvfi_csr_mepc_rdata    ,
  output logic [31:0] rvfi_csr_mepc_wdata    ,
  output logic [31:0] rvfi_csr_mtvec_rmask   ,
  output logic [31:0] rvfi_csr_mtvec_wmask   ,
  output logic [31:0] rvfi_csr_mtvec_rdata   ,
  output logic [31:0] rvfi_csr_mtvec_wdata   ,
`endif
  // to instruction memory interface
  input        [31:0] imem_rdata_i           ,
  output logic [31:0] imem_addr_o            ,
  // to data memory and peripheral interface
  input        [31:0] mem_rdata_i            ,
  input               mem_done_i             ,
  output              mem_valid_o            ,
  output logic        mem_wen_o              ,
  output logic [31:0] mem_addr_o             ,
  output logic [31:0] mem_wdata_o            ,
  output logic [ 3:0] mem_strb_o
);


// ---------------- IF/ID PIPELINE REGISTERS ----------------
// Going in / Coming out
  logic        if_d_valid, id_q_valid;
  logic [31:0] if_d_pc, id_q_pc;
  logic [31:0] if_d_pc_plus_4, id_q_pc_plus_4;
  logic [31:0] if_d_insn, id_q_insn;
`ifdef RISCV_FORMAL
  logic if_d_intr, id_q_intr;
`endif

// ---------------- ID/EX PIPELINE REGISTERS ----------------
// Going in / Coming out
  logic        id_d_valid, ex_q_valid;
  logic [31:0] id_d_pc, ex_q_pc;
  logic [31:0] id_d_pc_plus_4, ex_q_pc_plus_4;
  logic [ 4:0] id_d_rs1_addr, ex_q_rs1_addr;
  logic [ 4:0] id_d_rs2_addr, ex_q_rs2_addr;
  logic [ 4:0] id_d_rd_addr, ex_q_rd_addr;
  logic [31:0] id_d_rs1_rdata, ex_q_rs1_rdata;
  logic [31:0] id_d_rs2_rdata, ex_q_rs2_rdata;
  logic [31:0] id_d_imm_ext, ex_q_imm_ext;
  logic [11:0] id_d_csr_addr, ex_q_csr_addr;
  logic [31:0] id_d_csr_rdata, ex_q_csr_rdata;

  logic [       ALU_CTRL_T_WIDTH-1:0] id_d_alu_control, ex_q_alu_control;
  logic [      ALU_A_SEL_T_WIDTH-1:0] id_d_alu_a_sel, ex_q_alu_a_sel;
  logic [      ALU_B_SEL_T_WIDTH-1:0] id_d_alu_b_sel, ex_q_alu_b_sel;
  logic [     PC_ALU_SEL_T_WIDTH-1:0] id_d_pc_alu_sel, ex_q_pc_alu_sel;
  logic [CSR_BITMASK_SEL_T_WIDTH-1:0] id_d_csr_bitmask_sel, ex_q_csr_bitmask_sel;

  logic id_d_is_branch, ex_q_is_branch;
  logic id_d_is_jump, ex_q_is_jump;
  logic id_d_is_csr_write, ex_q_is_csr_write;
  logic id_d_is_csr_read, ex_q_is_csr_read;
  logic id_d_is_rd_write, ex_q_is_rd_write;
  logic id_d_is_rs1_read, ex_q_is_rs1_read;
  logic id_d_is_rs2_read, ex_q_is_rs2_read;
  logic id_d_is_mem_write, ex_q_is_mem_write;
  logic id_d_is_mem_read, ex_q_is_mem_read;

  logic id_d_is_jal, ex_q_is_jal;
  logic id_d_is_jalr, ex_q_is_jalr;
  logic id_d_is_memsize_b, ex_q_is_memsize_b;
  logic id_d_is_memsize_bu, ex_q_is_memsize_bu;
  logic id_d_is_memsize_h, ex_q_is_memsize_h;
  logic id_d_is_memsize_hu, ex_q_is_memsize_hu;
  logic id_d_is_memsize_w, ex_q_is_memsize_w;

  logic id_d_csr_op_rw, ex_q_csr_op_rw;
  logic id_d_csr_op_clear, ex_q_csr_op_clear;
  logic id_d_csr_op_set, ex_q_csr_op_set;

  logic       id_d_branch_predict, ex_q_branch_predict;
  logic [5:0] id_d_pht_idx, ex_q_pht_idx;

  logic        id_d_trap_valid, ex_q_trap_valid;
  logic [31:0] id_d_trap_mcause, ex_q_trap_mcause;
  logic [31:0] id_d_trap_pc, ex_q_trap_pc;

`ifdef RISCV_FORMAL
  logic [31:0] id_d_insn, ex_q_insn;
  logic        id_d_intr, ex_q_intr;
// For rvfi_trap_info, you can either flatten all fields or leave as separate regs
  logic [31:0] id_d_trap_insn,     ex_q_trap_insn;
  logic [31:0] id_d_trap_next_pc,  ex_q_trap_next_pc;
  logic [ 4:0] id_d_trap_rs1_addr, ex_q_trap_rs1_addr;
  logic [ 4:0] id_d_trap_rs2_addr, ex_q_trap_rs2_addr;
  logic [ 4:0] id_d_trap_rd_addr,  ex_q_trap_rd_addr;
  logic [31:0] id_d_trap_rs1_rdata, ex_q_trap_rs1_rdata;
  logic [31:0] id_d_trap_rs2_rdata, ex_q_trap_rs2_rdata;
  logic [31:0] id_d_trap_rd_wdata, ex_q_trap_rd_wdata;

`endif
// ---------------- EX/MEM PIPELINE REGISTERS ----------------
// Going in / Coming out
  logic        ex_d_valid,          mem_q_valid;
  logic [31:0] ex_d_pc,             mem_q_pc;
  logic [31:0] ex_d_pc_plus_4,      mem_q_pc_plus_4;
  logic [ 4:0] ex_d_rd_addr,        mem_q_rd_addr;
  logic [11:0] ex_d_csr_addr,       mem_q_csr_addr;
  logic [31:0] ex_d_csr_wdata,      mem_q_csr_wdata;

  logic [31:0] ex_d_store_wdata,    mem_q_store_wdata;
  logic [31:0] ex_d_alu_csr_result, mem_q_alu_csr_result;

  logic ex_d_is_branch,      mem_q_is_branch;
  logic ex_d_is_jump,        mem_q_is_jump;
  logic ex_d_is_csr_write,   mem_q_is_csr_write;
  logic ex_d_is_csr_read,    mem_q_is_csr_read;
  logic ex_d_is_rd_write,    mem_q_is_rd_write;
  logic ex_d_is_mem_write,   mem_q_is_mem_write;
  logic ex_d_is_mem_read,    mem_q_is_mem_read;

  logic ex_d_is_jal,         mem_q_is_jal;
  logic ex_d_is_jalr,        mem_q_is_jalr;
  logic ex_d_is_memsize_b,   mem_q_is_memsize_b;
  logic ex_d_is_memsize_bu,  mem_q_is_memsize_bu;
  logic ex_d_is_memsize_h,   mem_q_is_memsize_h;
  logic ex_d_is_memsize_hu,  mem_q_is_memsize_hu;
  logic ex_d_is_memsize_w,   mem_q_is_memsize_w;

  logic       ex_d_branch_predict, mem_q_branch_predict;
  logic [5:0] ex_d_pht_idx,        mem_q_pht_idx;

  logic        ex_d_jump_taken,     mem_q_jump_taken;
  logic [31:0] ex_d_jaddr,          mem_q_jaddr;

  logic        ex_d_trap_valid,     mem_q_trap_valid;
  logic [31:0] ex_d_trap_mcause,    mem_q_trap_mcause;
  logic [31:0] ex_d_trap_pc,        mem_q_trap_pc;

`ifdef RISCV_FORMAL
  logic [31:0] ex_d_insn,           mem_q_insn;
  logic        ex_d_intr,           mem_q_intr;
  logic [31:0] ex_d_next_pc,        mem_q_next_pc;
  logic [31:0] ex_d_csr_rdata,      mem_q_csr_rdata;
  logic [ 4:0] ex_d_rs1_addr,       mem_q_rs1_addr;
  logic [ 4:0] ex_d_rs2_addr,       mem_q_rs2_addr;
  logic [31:0] ex_d_rs1_rdata,      mem_q_rs1_rdata;
  logic [31:0] ex_d_rs2_rdata,      mem_q_rs2_rdata;
// Flattened trap_info_t inside ex_mem_t
  logic [31:0] ex_d_trap_insn,      mem_q_trap_insn;
  logic [31:0] ex_d_trap_next_pc,   mem_q_trap_next_pc;
  logic [ 4:0] ex_d_trap_rs1_addr,  mem_q_trap_rs1_addr;
  logic [ 4:0] ex_d_trap_rs2_addr,  mem_q_trap_rs2_addr;
  logic [ 4:0] ex_d_trap_rd_addr,   mem_q_trap_rd_addr;
  logic [31:0] ex_d_trap_rs1_rdata, mem_q_trap_rs1_rdata;
  logic [31:0] ex_d_trap_rs2_rdata, mem_q_trap_rs2_rdata;
  logic [31:0] ex_d_trap_rd_wdata,  mem_q_trap_rd_wdata;
`endif

// ---------------- MEM/WB PIPELINE REGISTERS ----------------
// Going in / Coming out
  logic        mem_d_valid,        wb_q_valid;
  logic [ 4:0] mem_d_rd_addr,      wb_q_rd_addr;
  logic [11:0] mem_d_csr_addr,     wb_q_csr_addr;
  logic [31:0] mem_d_csr_wdata,    wb_q_csr_wdata;
  logic [31:0] mem_d_rd_wdata,     wb_q_rd_wdata;
  logic [31:0] mem_d_pc_plus_4,    wb_q_pc_plus_4;

  logic mem_d_is_csr_write, wb_q_is_csr_write;
  logic mem_d_is_csr_read,  wb_q_is_csr_read;
  logic mem_d_is_rd_write,  wb_q_is_rd_write;

  logic        mem_d_trap_valid,   wb_q_trap_valid;
  logic [31:0] mem_d_trap_mcause,  wb_q_trap_mcause;
  logic [31:0] mem_d_trap_pc,      wb_q_trap_pc;

`ifdef RISCV_FORMAL
  logic [31:0] mem_d_pc,           wb_q_pc;
  logic [31:0] mem_d_next_pc,      wb_q_next_pc;
  logic [31:0] mem_d_insn,         wb_q_insn;
  logic        mem_d_intr,         wb_q_intr;
  logic [31:0] mem_d_csr_rdata,    wb_q_csr_rdata;
  logic [31:0] mem_d_mem_addr,     wb_q_mem_addr;
  logic [31:0] mem_d_load_rdata,   wb_q_load_rdata;
  logic [ 4:0] mem_d_rs1_addr,     wb_q_rs1_addr;
  logic [ 4:0] mem_d_rs2_addr,     wb_q_rs2_addr;
  logic [31:0] mem_d_rs1_rdata,    wb_q_rs1_rdata;
  logic [31:0] mem_d_rs2_rdata,    wb_q_rs2_rdata;
  logic [ 3:0] mem_d_load_rmask,   wb_q_load_rmask;
  logic [ 3:0] mem_d_store_wmask,  wb_q_store_wmask;
  logic [31:0] mem_d_store_wdata,  wb_q_store_wdata;
// Flattened trap_info_t inside mem_wb_t
  logic [31:0] mem_d_trap_insn,    wb_q_trap_insn;
  logic [31:0] mem_d_trap_next_pc, wb_q_trap_next_pc;
  logic [ 4:0] mem_d_trap_rs1_addr,wb_q_trap_rs1_addr;
  logic [ 4:0] mem_d_trap_rs2_addr,wb_q_trap_rs2_addr;
  logic [ 4:0] mem_d_trap_rd_addr, wb_q_trap_rd_addr;
  logic [31:0] mem_d_trap_rs1_rdata, wb_q_trap_rs1_rdata;
  logic [31:0] mem_d_trap_rs2_rdata, wb_q_trap_rs2_rdata;
  logic [31:0] mem_d_trap_rd_wdata, wb_q_trap_rd_wdata;
`endif


// ---------------- WB/RVFI PIPELINE REGISTERS ----------------
// Coming out



  logic if_id_stall;
  logic if_id_flush;

  logic id_ex_stall;
  logic id_ex_flush;

  logic ex_mem_stall;
  logic ex_mem_flush;

  logic mem_wb_stall;
  logic mem_wb_flush;
`ifdef RISCV_FORMAL

  logic [31:0] wb_csr_rmask;
  logic [31:0] wb_csr_wmask;
`endif
  // if stage signals;
  logic [31:0] next_pc          ;
  logic [31:0] trap_handler_addr;
  logic [31:0] imem_addr_q      ;
  logic        imem_rdata_valid ;
  logic        imem_buf_valid   ;
  logic [31:0] if_insn_buf      ;
  logic [31:0] if_buf_pc        ;
  // branch prediction logic
  logic [31:0] id_branch_addr   ;
  logic        id_predict_btaken;
  logic [ 5:0] id_pht_idx       ;
  // id stage signals
  logic                               id_forward_rs1       ;
  logic                               id_forward_rs2       ;
  logic [                       11:0] id_csr_addr          ;
  logic [                       31:0] id_imm_ext           ;
  logic [                        4:0] id_rd_addr           ;
  logic [       ALU_CTRL_T_WIDTH-1:0] id_alu_control       ;
  logic [                        6:0] id_op                ;
  logic [                        2:0] id_funct3            ;
  logic                               id_funct7b5          ;
  logic [                        6:0] id_funct7            ;
  logic [                       11:0] id_funct12           ;
  logic                               id_rtype_alt         ;
  logic                               id_itype_alt         ;
  logic [     IMM_EXT_OP_T_WIDTH-1:0] id_imm_ext_op        ;
  logic [      ALU_A_SEL_T_WIDTH-1:0] id_alu_a_sel         ;
  logic [      ALU_B_SEL_T_WIDTH-1:0] id_alu_b_sel         ;
  logic [     PC_ALU_SEL_T_WIDTH-1:0] id_pc_alu_sel        ;
  logic [CSR_BITMASK_SEL_T_WIDTH-1:0] id_csr_bitmask_sel   ;
  logic [                        4:0] id_rs1_addr          ;
  logic [                        4:0] id_rs2_addr          ;
  logic [                       31:0] regfile_rs1_rdata    ;
  logic [                       31:0] regfile_rs2_rdata    ;
  logic [                       31:0] csrfile_rdata        ;
  logic                               id_illegal_instr_trap;
  logic                               id_ecall_m_trap      ;
  logic                               id_breakpoint_trap   ;
  logic                               id_is_branch         ;
  logic                               id_is_jump           ;
  logic                               id_is_csr_write      ;
  logic                               id_is_csr_read       ;
  logic                               id_is_rd_write       ;
  logic                               id_is_rs1_read       ;
  logic                               id_is_rs2_read       ;
  logic                               id_is_mem_write      ;
  logic                               id_is_mem_read       ;
  logic                               id_is_jal            ;
  logic                               id_is_jalr           ;
  logic                               id_is_memsize_b      ;
  logic                               id_is_memsize_bu     ;
  logic                               id_is_memsize_h      ;
  logic                               id_is_memsize_hu     ;
  logic                               id_is_memsize_w      ;
  logic                               id_csr_op_rw         ;
  logic                               id_csr_op_clear      ;
  logic                               id_csr_op_set        ;

  // ex stage signal
  logic [ 1:0] ex_forward_rs1_sel;
  logic [ 1:0] ex_forward_rs2_sel;
  logic [31:0] ex_jaddr          ;
  logic        ex_jump_taken     ;
  logic [31:0] ex_rs1_rdata      ;
  logic [31:0] ex_rs2_rdata      ;
  logic [31:0] ex_csr_bitmask    ;
  logic [31:0] ex_csr_wdata      ;
  logic [31:0] ex_src_a          ;
  logic [31:0] ex_src_b          ;
  logic [31:0] ex_pc_base        ;
  logic        ex_branch_cond    ;
  logic        ex_misaligned_jump;
  logic [31:0] ex_alu_result     ;

  //mem stage
  logic        misaligned_load       ;
  logic        misaligned_store      ;
  logic [ 3:0] mem_wstrb             ;
  logic [ 3:0] mem_rstrb             ;
  logic        dmem_periph_req       ;
  logic [31:0] mem_load_rdata        ;
  logic        mem_btaken_mispredict ;
  logic        mem_bntaken_mispredict;
  logic        mem_branch_mispredict ;
  // writeback stage
  logic [ 4:0] wb_rd_addr    ;
  logic [11:0] wb_csr_addr   ;
  logic [31:0] wb_rd_wdata   ;
  logic [31:0] wb_csr_wdata  ;
  logic [31:0] wb_trap_mcause;
  logic [31:0] wb_trap_pc    ;
  //*****************************************************************
  //
  //
  // INSTRUCTION FETCH STAGE
  //
  //
  //*****************************************************************

  if_stage if_stage_inst (
    .clk_i                 (clk_i                 ),
    .rst_i                 (rst_i                 ),
    .if_id_flush           (if_id_flush           ),
    .if_id_stall           (if_id_stall           ),
    .wb_q_trap_valid       (wb_q_trap_valid       ),
    .trap_handler_addr     (trap_handler_addr     ),
    .mem_btaken_mispredict (mem_btaken_mispredict ),
    .mem_bntaken_mispredict(mem_bntaken_mispredict),
    .mem_q_pc_plus_4       (mem_q_pc_plus_4       ),
    .mem_q_jaddr           (mem_q_jaddr           ),
    .mem_q_jump_taken      (mem_q_jump_taken      ),
    .mem_q_is_branch       (mem_q_is_branch       ),
    .id_predict_btaken     (id_predict_btaken     ),
    .id_branch_addr        (id_branch_addr        ),
    .imem_rdata_i          (imem_rdata_i          ),
    .imem_addr_o           (imem_addr_o           ),
    .if_d_pc               (if_d_pc               ),
    .if_d_pc_plus_4        (if_d_pc_plus_4        ),
    .if_d_insn             (if_d_insn             ),
    .if_d_valid            (if_d_valid            ),
    .next_pc               (next_pc               ),
    .imem_rdata_valid      (imem_rdata_valid      )
    `ifdef RISCV_FORMAL
    ,
    .if_d_intr             (if_d_intr             )
    `endif
  );
  //*****************************************************************
  //
  //
  // INSTRUCTION DECODE STAGE
  //
  //
  //*****************************************************************

  branch_predictor branch_predictor_inst (
    .clk_i            (clk_i            ),
    .rst_i            (rst_i            ),
    .id_is_branch     (id_d_is_branch   ),
    .id_q_pc          (id_q_pc          ),
    .mem_q_is_branch  (mem_q_is_branch  ),
    .mem_q_jump_taken (mem_q_jump_taken ),
    .mem_q_pht_idx    (mem_q_pht_idx    ),
    .id_predict_btaken(id_predict_btaken),
    .id_pht_idx       (id_pht_idx       )
  );
id_stage  id_stage_inst (
    .id_q_insn(id_q_insn),
    .id_forward_rs1(id_forward_rs1),
    .id_forward_rs2(id_forward_rs2),
    .id_q_intr(id_q_intr),
    .id_q_pc(id_q_pc),
    .id_predict_btaken(id_predict_btaken),
    .id_pht_idx(id_pht_idx),
    .id_q_valid(id_q_valid),
    .id_q_pc_plus_4(id_q_pc_plus_4),
    .wb_rd_wdata(wb_rd_wdata),
    .regfile_rs1_rdata(regfile_rs1_rdata),
    .regfile_rs2_rdata(regfile_rs2_rdata),
    .csrfile_rdata(csrfile_rdata),
    .id_branch_addr(id_branch_addr),
    .id_d_is_branch(id_d_is_branch),
    .id_d_is_jump(id_d_is_jump),
    .id_d_is_jal(id_d_is_jal),
    .id_d_is_jalr(id_d_is_jalr),
    .id_d_branch_predict(id_d_branch_predict),
    .id_d_pht_idx(id_d_pht_idx),
    .id_d_is_csr_write(id_d_is_csr_write),
    .id_d_is_csr_read(id_d_is_csr_read),
    .id_d_csr_op_rw(id_d_csr_op_rw),
    .id_d_csr_op_clear(id_d_csr_op_clear),
    .id_d_csr_op_set(id_d_csr_op_set),
    .id_d_is_rd_write(id_d_is_rd_write),
    .id_d_is_rs1_read(id_d_is_rs1_read),
    .id_d_is_rs2_read(id_d_is_rs2_read),
    .id_d_is_mem_write(id_d_is_mem_write),
    .id_d_is_mem_read(id_d_is_mem_read),
    .id_d_is_memsize_b(id_d_is_memsize_b),
    .id_d_is_memsize_bu(id_d_is_memsize_bu),
    .id_d_is_memsize_h(id_d_is_memsize_h),
    .id_d_is_memsize_hu(id_d_is_memsize_hu),
    .id_d_is_memsize_w(id_d_is_memsize_w),
    .id_d_valid(id_d_valid),
    .id_d_pc(id_d_pc),
    .id_d_pc_plus_4(id_d_pc_plus_4),
    .id_d_rs1_addr(id_d_rs1_addr),
    .id_d_rs2_addr(id_d_rs2_addr),
    .id_d_rd_addr(id_d_rd_addr),
    .id_d_rs1_rdata(id_d_rs1_rdata),
    .id_d_rs2_rdata(id_d_rs2_rdata),
    .id_d_imm_ext(id_d_imm_ext),
    .id_d_csr_addr(id_d_csr_addr),
    .id_d_csr_rdata(id_d_csr_rdata),
    .id_d_alu_control(id_d_alu_control),
    .id_d_alu_a_sel(id_d_alu_a_sel),
    .id_d_alu_b_sel(id_d_alu_b_sel),
    .id_d_pc_alu_sel(id_d_pc_alu_sel),
    .id_d_csr_bitmask_sel(id_d_csr_bitmask_sel),
    .id_d_trap_valid(id_d_trap_valid),
    .id_d_trap_pc(id_d_trap_pc),
    .id_d_trap_mcause(id_d_trap_mcause)
    `ifdef RISCV_FORMAL
    ,
    .id_d_insn(id_d_insn),
    .id_d_intr(id_d_intr),
    .id_d_trap_insn(id_d_trap_insn),
    .id_d_trap_next_pc(id_d_trap_next_pc),
    .id_d_trap_rs1_addr(id_d_trap_rs1_addr),
    .id_d_trap_rs2_addr(id_d_trap_rs2_addr),
    .id_d_trap_rd_addr(id_d_trap_rd_addr),
    .id_d_trap_rs1_rdata(id_d_trap_rs1_rdata),
    .id_d_trap_rs2_rdata(id_d_trap_rs2_rdata),
    .id_d_trap_rd_wdata(id_d_trap_rd_wdata)
    `endif
  );



  //*****************************************************************
  //
  //
  // INSTRUCTION EXECUTE STAGE
  //
  //
  //*****************************************************************

  ex_stage ex_stage_inst (
    .clk_i               (clk_i               ),
    .rst_i               (rst_i               ),
    .ex_q_valid          (ex_q_valid          ),
    .ex_q_pc             (ex_q_pc             ),
    .ex_q_pc_plus_4      (ex_q_pc_plus_4      ),
    .ex_q_rs1_rdata      (ex_q_rs1_rdata      ),
    .ex_q_rs2_rdata      (ex_q_rs2_rdata      ),
    .ex_q_rs1_addr       (ex_q_rs1_addr       ),
    .ex_q_rs2_addr       (ex_q_rs2_addr       ),
    .ex_q_rd_addr        (ex_q_rd_addr        ),
    .ex_q_is_rd_write    (ex_q_is_rd_write    ),
    .ex_q_pht_idx        (ex_q_pht_idx        ),
    .ex_q_is_csr_write   (ex_q_is_csr_write   ),
    .ex_q_is_csr_read    (ex_q_is_csr_read    ),
    .ex_q_csr_addr       (ex_q_csr_addr       ),
    .ex_q_csr_rdata      (ex_q_csr_rdata      ),
    .ex_q_imm_ext        (ex_q_imm_ext        ),
    .ex_q_insn           (ex_q_insn           ),
    .ex_q_intr           (ex_q_intr           ),
    .ex_q_is_jump        (ex_q_is_jump        ),
    .ex_q_is_jal         (ex_q_is_jal         ),
    .ex_q_is_jalr        (ex_q_is_jalr        ),
    .ex_q_is_branch      (ex_q_is_branch      ),
    .ex_q_branch_predict (ex_q_branch_predict ),
    .ex_q_alu_control    (ex_q_alu_control    ),
    .ex_q_alu_a_sel      (ex_q_alu_a_sel      ),
    .ex_q_alu_b_sel      (ex_q_alu_b_sel      ),
    .ex_q_pc_alu_sel     (ex_q_pc_alu_sel     ),
    .ex_q_csr_bitmask_sel(ex_q_csr_bitmask_sel),
    .ex_q_csr_op_rw      (ex_q_csr_op_rw      ),
    .ex_q_csr_op_set     (ex_q_csr_op_set     ),
    .ex_q_csr_op_clear   (ex_q_csr_op_clear   ),
    .ex_q_is_mem_read    (ex_q_is_mem_read    ),
    .ex_q_is_mem_write   (ex_q_is_mem_write   ),
    .ex_q_is_memsize_b   (ex_q_is_memsize_b   ),
    .ex_q_is_memsize_bu  (ex_q_is_memsize_bu  ),
    .ex_q_is_memsize_h   (ex_q_is_memsize_h   ),
    .ex_q_is_memsize_hu  (ex_q_is_memsize_hu  ),
    .ex_q_is_memsize_w   (ex_q_is_memsize_w   ),
    .ex_q_trap_valid     (ex_q_trap_valid     ),
    .ex_q_trap_pc        (ex_q_trap_pc        ),
    .ex_q_trap_mcause    (ex_q_trap_mcause    ),
    .ex_q_trap_insn      (ex_q_trap_insn      ),
    .ex_q_trap_next_pc   (ex_q_trap_next_pc   ),
    .ex_q_trap_rs1_addr  (ex_q_trap_rs1_addr  ),
    .ex_q_trap_rs2_addr  (ex_q_trap_rs2_addr  ),
    .ex_q_trap_rd_addr   (ex_q_trap_rd_addr   ),
    .ex_q_trap_rs1_rdata (ex_q_trap_rs1_rdata ),
    .ex_q_trap_rs2_rdata (ex_q_trap_rs2_rdata ),
    .ex_q_trap_rd_wdata  (ex_q_trap_rd_wdata  ),
    .mem_q_alu_csr_result(mem_q_alu_csr_result),
    .wb_rd_wdata         (wb_rd_wdata         ),
    .ex_forward_rs1_sel  (ex_forward_rs1_sel  ),
    .ex_forward_rs2_sel  (ex_forward_rs2_sel  ),
    .ex_d_valid          (ex_d_valid          ),
    .ex_d_is_rd_write    (ex_d_is_rd_write    ),
    .ex_d_rd_addr        (ex_d_rd_addr        ),
    .ex_d_is_csr_write   (ex_d_is_csr_write   ),
    .ex_d_is_csr_read    (ex_d_is_csr_read    ),
    .ex_d_csr_addr       (ex_d_csr_addr       ),
    .ex_d_csr_wdata      (ex_d_csr_wdata      ),
    .ex_d_store_wdata    (ex_d_store_wdata    ),
    .ex_d_alu_csr_result (ex_d_alu_csr_result ),
    .ex_d_is_mem_read    (ex_d_is_mem_read    ),
    .ex_d_is_mem_write   (ex_d_is_mem_write   ),
    .ex_d_is_memsize_h   (ex_d_is_memsize_h   ),
    .ex_d_is_memsize_hu  (ex_d_is_memsize_hu  ),
    .ex_d_is_memsize_b   (ex_d_is_memsize_b   ),
    .ex_d_is_memsize_bu  (ex_d_is_memsize_bu  ),
    .ex_d_is_memsize_w   (ex_d_is_memsize_w   ),
    .ex_d_is_branch      (ex_d_is_branch      ),
    .ex_d_is_jump        (ex_d_is_jump        ),
    .ex_d_is_jal         (ex_d_is_jal         ),
    .ex_d_is_jalr        (ex_d_is_jalr        ),
    .ex_d_branch_predict (ex_d_branch_predict ),
    .ex_d_pht_idx        (ex_d_pht_idx        ),
    .ex_d_pc             (ex_d_pc             ),
    .ex_d_pc_plus_4      (ex_d_pc_plus_4      ),
    .ex_d_jaddr          (ex_d_jaddr          ),
    .ex_d_jump_taken     (ex_d_jump_taken     ),
    .ex_d_trap_valid     (ex_d_trap_valid     ),
    .ex_d_trap_pc        (ex_d_trap_pc        ),
    .ex_d_trap_mcause    (ex_d_trap_mcause    ),
    .ex_d_next_pc        (ex_d_next_pc        ),
    .ex_d_insn           (ex_d_insn           ),
    .ex_d_intr           (ex_d_intr           ),
    .ex_d_rs1_addr       (ex_d_rs1_addr       ),
    .ex_d_rs2_addr       (ex_d_rs2_addr       ),
    .ex_d_rs1_rdata      (ex_d_rs1_rdata      ),
    .ex_d_rs2_rdata      (ex_d_rs2_rdata      ),
    .ex_d_csr_rdata      (ex_d_csr_rdata      ),
    .ex_d_trap_insn      (ex_d_trap_insn      ),
    .ex_d_trap_next_pc   (ex_d_trap_next_pc   ),
    .ex_d_trap_rs1_addr  (ex_d_trap_rs1_addr  ),
    .ex_d_trap_rs2_addr  (ex_d_trap_rs2_addr  ),
    .ex_d_trap_rd_addr   (ex_d_trap_rd_addr   ),
    .ex_d_trap_rs1_rdata (ex_d_trap_rs1_rdata ),
    .ex_d_trap_rs2_rdata (ex_d_trap_rs2_rdata ),
    .ex_d_trap_rd_wdata  (ex_d_trap_rd_wdata  )
  );
  //*****************************************************************
  //
  //
  // DATA MEMORY STAGE
  //
  //
  //*****************************************************************
  mem_stage mem_stage_inst (
    .clk_i                 (clk_i                 ),
    .rst_i                 (rst_i                 ),
    .mem_q_pc              (mem_q_pc              ),
    .mem_q_next_pc         (mem_q_next_pc         ),
    .mem_q_insn            (mem_q_insn            ),
    .mem_q_intr            (mem_q_intr            ),
    .mem_q_valid           (mem_q_valid           ),
    .mem_q_store_wdata     (mem_q_store_wdata     ),
    .mem_q_is_rd_write     (mem_q_is_rd_write     ),
    .mem_q_rd_addr         (mem_q_rd_addr         ),
    .mem_q_is_csr_write    (mem_q_is_csr_write    ),
    .mem_q_is_csr_read     (mem_q_is_csr_read     ),
    .mem_q_csr_addr        (mem_q_csr_addr        ),
    .mem_q_csr_wdata       (mem_q_csr_wdata       ),
    .mem_q_csr_rdata       (mem_q_csr_rdata       ),
    .mem_q_alu_csr_result  (mem_q_alu_csr_result  ),
    .mem_q_is_mem_read     (mem_q_is_mem_read     ),
    .mem_q_is_mem_write    (mem_q_is_mem_write    ),
    .mem_q_is_memsize_w    (mem_q_is_memsize_w    ),
    .mem_q_is_memsize_h    (mem_q_is_memsize_h    ),
    .mem_q_is_memsize_hu   (mem_q_is_memsize_hu   ),
    .mem_q_is_memsize_b    (mem_q_is_memsize_b    ),
    .mem_q_is_memsize_bu   (mem_q_is_memsize_bu   ),
    .mem_q_is_jal          (mem_q_is_jal          ),
    .mem_q_is_jalr         (mem_q_is_jalr         ),
    .mem_q_is_branch       (mem_q_is_branch       ),
    .mem_q_branch_predict  (mem_q_branch_predict  ),
    .mem_q_jump_taken      (mem_q_jump_taken      ),
    .mem_q_jaddr           (mem_q_jaddr           ),
    .mem_q_pc_plus_4       (mem_q_pc_plus_4       ),
    .mem_q_rs1_rdata       (mem_q_rs1_rdata       ),
    .mem_q_rs2_rdata       (mem_q_rs2_rdata       ),
    .mem_q_rs1_addr        (mem_q_rs1_addr        ),
    .mem_q_rs2_addr        (mem_q_rs2_addr        ),
    .mem_q_trap_valid      (mem_q_trap_valid      ),
    .mem_q_trap_insn       (mem_q_trap_insn       ),
    .mem_q_trap_pc         (mem_q_trap_pc         ),
    .mem_q_trap_next_pc    (mem_q_trap_next_pc    ),
    .mem_q_trap_rs1_addr   (mem_q_trap_rs1_addr   ),
    .mem_q_trap_rs2_addr   (mem_q_trap_rs2_addr   ),
    .mem_q_trap_rd_addr    (mem_q_trap_rd_addr    ),
    .mem_q_trap_rs1_rdata  (mem_q_trap_rs1_rdata  ),
    .mem_q_trap_rs2_rdata  (mem_q_trap_rs2_rdata  ),
    .trap_handler_addr     (trap_handler_addr     ),
    .mem_q_trap_mcause     (mem_q_trap_mcause     ),
    .mem_rdata_i           (mem_rdata_i           ),
    .mem_strb_o            (mem_strb_o            ),
    .mem_addr_o            (mem_addr_o            ),
    .mem_wdata_o           (mem_wdata_o           ),
    .mem_wen_o             (mem_wen_o             ),
    .mem_valid_o           (mem_valid_o           ),
    .dmem_periph_req       (dmem_periph_req       ),
    .mem_done_i            (mem_done_i            ),
    .mem_d_valid           (mem_d_valid           ),
    .mem_d_is_rd_write     (mem_d_is_rd_write     ),
    .mem_d_rd_addr         (mem_d_rd_addr         ),
    .mem_d_rd_wdata        (mem_d_rd_wdata        ),
    .mem_d_is_csr_write    (mem_d_is_csr_write    ),
    .mem_d_is_csr_read     (mem_d_is_csr_read     ),
    .mem_d_csr_addr        (mem_d_csr_addr        ),
    .mem_d_csr_wdata       (mem_d_csr_wdata       ),
    .mem_d_pc_plus_4       (mem_d_pc_plus_4       ),
    .mem_d_trap_valid      (mem_d_trap_valid      ),
    .mem_d_trap_pc         (mem_d_trap_pc         ),
    .mem_d_trap_mcause     (mem_d_trap_mcause     ),
    .mem_btaken_mispredict (mem_btaken_mispredict ),
    .mem_bntaken_mispredict(mem_bntaken_mispredict),
    .mem_branch_mispredict (mem_branch_mispredict )
    `ifdef RISCV_FORMAL
    ,
    .mem_d_pc              (mem_d_pc              ),
    .mem_d_next_pc         (mem_d_next_pc         ),
    .mem_d_insn            (mem_d_insn            ),
    .mem_d_intr            (mem_d_intr            ),
    .mem_d_rs1_addr        (mem_d_rs1_addr        ),
    .mem_d_rs2_addr        (mem_d_rs2_addr        ),
    .mem_d_rs1_rdata       (mem_d_rs1_rdata       ),
    .mem_d_rs2_rdata       (mem_d_rs2_rdata       ),
    .mem_d_mem_addr        (mem_d_mem_addr        ),
    .mem_d_load_rmask      (mem_d_load_rmask      ),
    .mem_d_store_wmask     (mem_d_store_wmask     ),
    .mem_d_store_wdata     (mem_d_store_wdata     ),
    .mem_d_csr_rdata       (mem_d_csr_rdata       ),
    .mem_d_load_rdata      (mem_d_load_rdata      ),
    .mem_d_trap_insn       (mem_d_trap_insn       ),
    .mem_d_trap_next_pc    (mem_d_trap_next_pc    ),
    .mem_d_trap_rs1_addr   (mem_d_trap_rs1_addr   ),
    .mem_d_trap_rs2_addr   (mem_d_trap_rs2_addr   ),
    .mem_d_trap_rd_addr    (mem_d_trap_rd_addr    ),
    .mem_d_trap_rs1_rdata  (mem_d_trap_rs1_rdata  ),
    .mem_d_trap_rs2_rdata  (mem_d_trap_rs2_rdata  ),
    .mem_d_trap_rd_wdata   (mem_d_trap_rd_wdata   )
    `endif
  );
  //*****************************************************************
  //
  //
  // WRITEBACK STAGE
  //
  //
  //*****************************************************************


  always_comb
    begin
      wb_trap_mcause = wb_q_trap_mcause;
      wb_trap_pc     = wb_q_trap_pc;
      wb_rd_addr     = wb_q_rd_addr;
      wb_rd_wdata    = wb_q_rd_wdata;
      wb_csr_addr    = wb_q_csr_addr;
      wb_csr_wdata   = wb_q_csr_wdata;
    end

  //*****************************************************************
  //
  //
  // PIPELINE REGISTERS
  //
  //
  //*****************************************************************


//-------------------------------
// IF/ID pipeline
//-------------------------------
  if_id_pipeline if_id_pipeline_inst (
    .clk_i           (clk_i           ),
    .rst_i           (rst_i           ),
    .if_id_flush     (if_id_flush     ),
    .if_id_stall     (if_id_stall     ),
    .imem_rdata_valid(imem_rdata_valid),
    .if_d_valid      (if_d_valid      ),
    .if_d_pc         (if_d_pc         ),
    .if_d_pc_plus_4  (if_d_pc_plus_4  ),
    .if_d_insn       (if_d_insn       ),
    `ifdef RISCV_FORMAL
    .if_d_intr       (if_d_intr       ),
    .id_q_intr       (id_q_intr       ),
    `endif
    .id_q_valid      (id_q_valid      ),
    .id_q_pc         (id_q_pc         ),
    .id_q_pc_plus_4  (id_q_pc_plus_4  ),
    .id_q_insn       (id_q_insn       )
  );


//-------------------------------
// ID/EX pipeline
//-------------------------------
  id_ex_pipeline id_ex_pipeline_inst (
    .clk_i               (clk_i               ),
    .rst_i               (rst_i               ),
    .id_ex_flush         (id_ex_flush         ),
    .id_ex_stall         (id_ex_stall         ),
    .if_id_stall         (if_id_stall         ),
    .id_d_valid          (id_d_valid          ),
    .id_d_pc             (id_d_pc             ),
    .id_d_pc_plus_4      (id_d_pc_plus_4      ),
    .id_d_rs1_addr       (id_d_rs1_addr       ),
    .id_d_rs2_addr       (id_d_rs2_addr       ),
    .id_d_rd_addr        (id_d_rd_addr        ),
    .id_d_rs1_rdata      (id_d_rs1_rdata      ),
    .id_d_rs2_rdata      (id_d_rs2_rdata      ),
    .id_d_imm_ext        (id_d_imm_ext        ),
    .id_d_csr_addr       (id_d_csr_addr       ),
    .id_d_csr_rdata      (id_d_csr_rdata      ),
    .id_d_alu_control    (id_d_alu_control    ),
    .id_d_alu_a_sel      (id_d_alu_a_sel      ),
    .id_d_alu_b_sel      (id_d_alu_b_sel      ),
    .id_d_pc_alu_sel     (id_d_pc_alu_sel     ),
    .id_d_csr_bitmask_sel(id_d_csr_bitmask_sel),
    .id_d_is_branch      (id_d_is_branch      ),
    .id_d_is_jump        (id_d_is_jump        ),
    .id_d_is_csr_write   (id_d_is_csr_write   ),
    .id_d_is_csr_read    (id_d_is_csr_read    ),
    .id_d_is_rd_write    (id_d_is_rd_write    ),
    .id_d_is_rs1_read    (id_d_is_rs1_read    ),
    .id_d_is_rs2_read    (id_d_is_rs2_read    ),
    .id_d_is_mem_write   (id_d_is_mem_write   ),
    .id_d_is_mem_read    (id_d_is_mem_read    ),
    .id_d_is_jal         (id_d_is_jal         ),
    .id_d_is_jalr        (id_d_is_jalr        ),
    .id_d_is_memsize_b   (id_d_is_memsize_b   ),
    .id_d_is_memsize_bu  (id_d_is_memsize_bu  ),
    .id_d_is_memsize_h   (id_d_is_memsize_h   ),
    .id_d_is_memsize_hu  (id_d_is_memsize_hu  ),
    .id_d_is_memsize_w   (id_d_is_memsize_w   ),
    .id_d_csr_op_rw      (id_d_csr_op_rw      ),
    .id_d_csr_op_clear   (id_d_csr_op_clear   ),
    .id_d_csr_op_set     (id_d_csr_op_set     ),
    .id_d_branch_predict (id_d_branch_predict ),
    .id_d_pht_idx        (id_d_pht_idx        ),
    .id_d_trap_valid     (id_d_trap_valid     ),
    .id_d_trap_mcause    (id_d_trap_mcause    ),
    .id_d_trap_pc        (id_d_trap_pc        ),
    .id_d_insn           (id_d_insn           ),
    .id_d_intr           (id_d_intr           ),
    .id_d_trap_insn      (id_d_trap_insn      ),
    .id_d_trap_next_pc   (id_d_trap_next_pc   ),
    .id_d_trap_rs1_addr  (id_d_trap_rs1_addr  ),
    .id_d_trap_rs2_addr  (id_d_trap_rs2_addr  ),
    .id_d_trap_rd_addr   (id_d_trap_rd_addr   ),
    .id_d_trap_rs1_rdata (id_d_trap_rs1_rdata ),
    .id_d_trap_rs2_rdata (id_d_trap_rs2_rdata ),
    .id_d_trap_rd_wdata  (id_d_trap_rd_wdata  ),
    .ex_q_insn           (ex_q_insn           ),
    .ex_q_intr           (ex_q_intr           ),
    .ex_q_trap_insn      (ex_q_trap_insn      ),
    .ex_q_trap_next_pc   (ex_q_trap_next_pc   ),
    .ex_q_trap_rs1_addr  (ex_q_trap_rs1_addr  ),
    .ex_q_trap_rs2_addr  (ex_q_trap_rs2_addr  ),
    .ex_q_trap_rd_addr   (ex_q_trap_rd_addr   ),
    .ex_q_trap_rs1_rdata (ex_q_trap_rs1_rdata ),
    .ex_q_trap_rs2_rdata (ex_q_trap_rs2_rdata ),
    .ex_q_trap_rd_wdata  (ex_q_trap_rd_wdata  ),
    .ex_q_valid          (ex_q_valid          ),
    .ex_q_pc             (ex_q_pc             ),
    .ex_q_pc_plus_4      (ex_q_pc_plus_4      ),
    .ex_q_rs1_addr       (ex_q_rs1_addr       ),
    .ex_q_rs2_addr       (ex_q_rs2_addr       ),
    .ex_q_rd_addr        (ex_q_rd_addr        ),
    .ex_q_rs1_rdata      (ex_q_rs1_rdata      ),
    .ex_q_rs2_rdata      (ex_q_rs2_rdata      ),
    .ex_q_imm_ext        (ex_q_imm_ext        ),
    .ex_q_csr_addr       (ex_q_csr_addr       ),
    .ex_q_csr_rdata      (ex_q_csr_rdata      ),
    .ex_q_alu_control    (ex_q_alu_control    ),
    .ex_q_alu_a_sel      (ex_q_alu_a_sel      ),
    .ex_q_alu_b_sel      (ex_q_alu_b_sel      ),
    .ex_q_pc_alu_sel     (ex_q_pc_alu_sel     ),
    .ex_q_csr_bitmask_sel(ex_q_csr_bitmask_sel),
    .ex_q_is_branch      (ex_q_is_branch      ),
    .ex_q_is_jump        (ex_q_is_jump        ),
    .ex_q_is_csr_write   (ex_q_is_csr_write   ),
    .ex_q_is_csr_read    (ex_q_is_csr_read    ),
    .ex_q_is_rd_write    (ex_q_is_rd_write    ),
    .ex_q_is_rs1_read    (ex_q_is_rs1_read    ),
    .ex_q_is_rs2_read    (ex_q_is_rs2_read    ),
    .ex_q_is_mem_write   (ex_q_is_mem_write   ),
    .ex_q_is_mem_read    (ex_q_is_mem_read    ),
    .ex_q_is_jal         (ex_q_is_jal         ),
    .ex_q_is_jalr        (ex_q_is_jalr        ),
    .ex_q_is_memsize_b   (ex_q_is_memsize_b   ),
    .ex_q_is_memsize_bu  (ex_q_is_memsize_bu  ),
    .ex_q_is_memsize_h   (ex_q_is_memsize_h   ),
    .ex_q_is_memsize_hu  (ex_q_is_memsize_hu  ),
    .ex_q_is_memsize_w   (ex_q_is_memsize_w   ),
    .ex_q_csr_op_rw      (ex_q_csr_op_rw      ),
    .ex_q_csr_op_clear   (ex_q_csr_op_clear   ),
    .ex_q_csr_op_set     (ex_q_csr_op_set     ),
    .ex_q_branch_predict (ex_q_branch_predict ),
    .ex_q_pht_idx        (ex_q_pht_idx        ),
    .ex_q_trap_valid     (ex_q_trap_valid     ),
    .ex_q_trap_mcause    (ex_q_trap_mcause    ),
    .ex_q_trap_pc        (ex_q_trap_pc        )
  );



//-------------------------------
// EX/MEM pipeline
//-------------------------------
  ex_mem_pipeline ex_mem_pipeline_inst (
    .clk_i               (clk_i               ),
    .rst_i               (rst_i               ),
    .ex_mem_flush        (ex_mem_flush        ),
    .ex_mem_stall        (ex_mem_stall        ),
    .id_ex_stall         (id_ex_stall         ),
    .ex_d_valid          (ex_d_valid          ),
    .ex_d_pc             (ex_d_pc             ),
    .ex_d_pc_plus_4      (ex_d_pc_plus_4      ),
    .ex_d_rd_addr        (ex_d_rd_addr        ),
    .ex_d_csr_addr       (ex_d_csr_addr       ),
    .ex_d_csr_wdata      (ex_d_csr_wdata      ),
    .ex_d_store_wdata    (ex_d_store_wdata    ),
    .ex_d_alu_csr_result (ex_d_alu_csr_result ),
    .ex_d_is_branch      (ex_d_is_branch      ),
    .ex_d_is_jump        (ex_d_is_jump        ),
    .ex_d_is_csr_write   (ex_d_is_csr_write   ),
    .ex_d_is_csr_read    (ex_d_is_csr_read    ),
    .ex_d_is_rd_write    (ex_d_is_rd_write    ),
    .ex_d_is_mem_write   (ex_d_is_mem_write   ),
    .ex_d_is_mem_read    (ex_d_is_mem_read    ),
    .ex_d_is_jal         (ex_d_is_jal         ),
    .ex_d_is_jalr        (ex_d_is_jalr        ),
    .ex_d_is_memsize_b   (ex_d_is_memsize_b   ),
    .ex_d_is_memsize_bu  (ex_d_is_memsize_bu  ),
    .ex_d_is_memsize_h   (ex_d_is_memsize_h   ),
    .ex_d_is_memsize_hu  (ex_d_is_memsize_hu  ),
    .ex_d_is_memsize_w   (ex_d_is_memsize_w   ),
    .ex_d_branch_predict (ex_d_branch_predict ),
    .ex_d_pht_idx        (ex_d_pht_idx        ),
    .ex_d_jump_taken     (ex_d_jump_taken     ),
    .ex_d_jaddr          (ex_d_jaddr          ),
    .ex_d_trap_valid     (ex_d_trap_valid     ),
    .ex_d_trap_mcause    (ex_d_trap_mcause    ),
    .ex_d_trap_pc        (ex_d_trap_pc        ),
    `ifdef RISCV_FORMAL
    .ex_d_insn           (ex_d_insn           ),
    .ex_d_intr           (ex_d_intr           ),
    .ex_d_next_pc        (ex_d_next_pc        ),
    .ex_d_csr_rdata      (ex_d_csr_rdata      ),
    .ex_d_rs1_addr       (ex_d_rs1_addr       ),
    .ex_d_rs2_addr       (ex_d_rs2_addr       ),
    .ex_d_rs1_rdata      (ex_d_rs1_rdata      ),
    .ex_d_rs2_rdata      (ex_d_rs2_rdata      ),
    .ex_d_trap_insn      (ex_d_trap_insn      ),
    .ex_d_trap_next_pc   (ex_d_trap_next_pc   ),
    .ex_d_trap_rs1_addr  (ex_d_trap_rs1_addr  ),
    .ex_d_trap_rs2_addr  (ex_d_trap_rs2_addr  ),
    .ex_d_trap_rd_addr   (ex_d_trap_rd_addr   ),
    .ex_d_trap_rs1_rdata (ex_d_trap_rs1_rdata ),
    .ex_d_trap_rs2_rdata (ex_d_trap_rs2_rdata ),
    .ex_d_trap_rd_wdata  (ex_d_trap_rd_wdata  ),
    .mem_q_insn          (mem_q_insn          ),
    .mem_q_intr          (mem_q_intr          ),
    .mem_q_next_pc       (mem_q_next_pc       ),
    .mem_q_csr_rdata     (mem_q_csr_rdata     ),
    .mem_q_rs1_addr      (mem_q_rs1_addr      ),
    .mem_q_rs2_addr      (mem_q_rs2_addr      ),
    .mem_q_rs1_rdata     (mem_q_rs1_rdata     ),
    .mem_q_rs2_rdata     (mem_q_rs2_rdata     ),
    .mem_q_trap_insn     (mem_q_trap_insn     ),
    .mem_q_trap_next_pc  (mem_q_trap_next_pc  ),
    .mem_q_trap_rs1_addr (mem_q_trap_rs1_addr ),
    .mem_q_trap_rs2_addr (mem_q_trap_rs2_addr ),
    .mem_q_trap_rd_addr  (mem_q_trap_rd_addr  ),
    .mem_q_trap_rs1_rdata(mem_q_trap_rs1_rdata),
    .mem_q_trap_rs2_rdata(mem_q_trap_rs2_rdata),
    .mem_q_trap_rd_wdata (mem_q_trap_rd_wdata ),
    `endif
    .mem_q_valid         (mem_q_valid         ),
    .mem_q_pc            (mem_q_pc            ),
    .mem_q_pc_plus_4     (mem_q_pc_plus_4     ),
    .mem_q_rd_addr       (mem_q_rd_addr       ),
    .mem_q_csr_addr      (mem_q_csr_addr      ),
    .mem_q_csr_wdata     (mem_q_csr_wdata     ),
    .mem_q_store_wdata   (mem_q_store_wdata   ),
    .mem_q_alu_csr_result(mem_q_alu_csr_result),
    .mem_q_is_branch     (mem_q_is_branch     ),
    .mem_q_is_jump       (mem_q_is_jump       ),
    .mem_q_is_csr_write  (mem_q_is_csr_write  ),
    .mem_q_is_csr_read   (mem_q_is_csr_read   ),
    .mem_q_is_rd_write   (mem_q_is_rd_write   ),
    .mem_q_is_mem_write  (mem_q_is_mem_write  ),
    .mem_q_is_mem_read   (mem_q_is_mem_read   ),
    .mem_q_is_jal        (mem_q_is_jal        ),
    .mem_q_is_jalr       (mem_q_is_jalr       ),
    .mem_q_is_memsize_b  (mem_q_is_memsize_b  ),
    .mem_q_is_memsize_bu (mem_q_is_memsize_bu ),
    .mem_q_is_memsize_h  (mem_q_is_memsize_h  ),
    .mem_q_is_memsize_hu (mem_q_is_memsize_hu ),
    .mem_q_is_memsize_w  (mem_q_is_memsize_w  ),
    .mem_q_branch_predict(mem_q_branch_predict),
    .mem_q_pht_idx       (mem_q_pht_idx       ),
    .mem_q_jump_taken    (mem_q_jump_taken    ),
    .mem_q_jaddr         (mem_q_jaddr         ),
    .mem_q_trap_valid    (mem_q_trap_valid    ),
    .mem_q_trap_mcause   (mem_q_trap_mcause   ),
    .mem_q_trap_pc       (mem_q_trap_pc       )
  );

//-------------------------------
// MEM/WB pipeline
//-------------------------------
  mem_wb_pipeline mem_wb_pipeline_inst (
    .clk_i               (clk_i               ),
    .rst_i               (rst_i               ),
    .mem_wb_flush        (mem_wb_flush        ),
    .mem_wb_stall        (mem_wb_stall        ),
    .ex_mem_stall        (ex_mem_stall        ),
    .mem_d_valid         (mem_d_valid         ),
    .mem_d_rd_addr       (mem_d_rd_addr       ),
    .mem_d_csr_addr      (mem_d_csr_addr      ),
    .mem_d_csr_wdata     (mem_d_csr_wdata     ),
    .mem_d_rd_wdata      (mem_d_rd_wdata      ),
    .mem_d_pc_plus_4     (mem_d_pc_plus_4     ),
    .mem_d_is_csr_write  (mem_d_is_csr_write  ),
    .mem_d_is_csr_read   (mem_d_is_csr_read   ),
    .mem_d_is_rd_write   (mem_d_is_rd_write   ),
    .mem_d_trap_valid    (mem_d_trap_valid    ),
    .mem_d_trap_mcause   (mem_d_trap_mcause   ),
    .mem_d_trap_pc       (mem_d_trap_pc       ),
    `ifdef RISCV_FORMAL
    .mem_d_pc            (mem_d_pc            ),
    .mem_d_next_pc       (mem_d_next_pc       ),
    .mem_d_insn          (mem_d_insn          ),
    .mem_d_intr          (mem_d_intr          ),
    .mem_d_csr_rdata     (mem_d_csr_rdata     ),
    .mem_d_mem_addr      (mem_d_mem_addr      ),
    .mem_d_load_rdata    (mem_d_load_rdata    ),
    .mem_d_rs1_addr      (mem_d_rs1_addr      ),
    .mem_d_rs2_addr      (mem_d_rs2_addr      ),
    .mem_d_rs1_rdata     (mem_d_rs1_rdata     ),
    .mem_d_rs2_rdata     (mem_d_rs2_rdata     ),
    .mem_d_load_rmask    (mem_d_load_rmask    ),
    .mem_d_store_wmask   (mem_d_store_wmask   ),
    .mem_d_store_wdata   (mem_d_store_wdata   ),
    .mem_d_trap_insn     (mem_d_trap_insn     ),
    .mem_d_trap_next_pc  (mem_d_trap_next_pc  ),
    .mem_d_trap_rs1_addr (mem_d_trap_rs1_addr ),
    .mem_d_trap_rs2_addr (mem_d_trap_rs2_addr ),
    .mem_d_trap_rd_addr  (mem_d_trap_rd_addr  ),
    .mem_d_trap_rs1_rdata(mem_d_trap_rs1_rdata),
    .mem_d_trap_rs2_rdata(mem_d_trap_rs2_rdata),
    .mem_d_trap_rd_wdata (mem_d_trap_rd_wdata ),
    .wb_q_pc             (wb_q_pc             ),
    .wb_q_next_pc        (wb_q_next_pc        ),
    .wb_q_insn           (wb_q_insn           ),
    .wb_q_intr           (wb_q_intr           ),
    .wb_q_csr_rdata      (wb_q_csr_rdata      ),
    .wb_q_mem_addr       (wb_q_mem_addr       ),
    .wb_q_load_rdata     (wb_q_load_rdata     ),
    .wb_q_rs1_addr       (wb_q_rs1_addr       ),
    .wb_q_rs2_addr       (wb_q_rs2_addr       ),
    .wb_q_rs1_rdata      (wb_q_rs1_rdata      ),
    .wb_q_rs2_rdata      (wb_q_rs2_rdata      ),
    .wb_q_load_rmask     (wb_q_load_rmask     ),
    .wb_q_store_wmask    (wb_q_store_wmask    ),
    .wb_q_store_wdata    (wb_q_store_wdata    ),
    .wb_q_trap_insn      (wb_q_trap_insn      ),
    .wb_q_trap_next_pc   (wb_q_trap_next_pc   ),
    .wb_q_trap_rs1_addr  (wb_q_trap_rs1_addr  ),
    .wb_q_trap_rs2_addr  (wb_q_trap_rs2_addr  ),
    .wb_q_trap_rd_addr   (wb_q_trap_rd_addr   ),
    .wb_q_trap_rs1_rdata (wb_q_trap_rs1_rdata ),
    .wb_q_trap_rs2_rdata (wb_q_trap_rs2_rdata ),
    .wb_q_trap_rd_wdata  (wb_q_trap_rd_wdata  ),
    `endif
    .wb_q_valid          (wb_q_valid          ),
    .wb_q_rd_addr        (wb_q_rd_addr        ),
    .wb_q_csr_addr       (wb_q_csr_addr       ),
    .wb_q_csr_wdata      (wb_q_csr_wdata      ),
    .wb_q_rd_wdata       (wb_q_rd_wdata       ),
    .wb_q_pc_plus_4      (wb_q_pc_plus_4      ),
    .wb_q_is_csr_write   (wb_q_is_csr_write   ),
    .wb_q_is_csr_read    (wb_q_is_csr_read    ),
    .wb_q_is_rd_write    (wb_q_is_rd_write    ),
    .wb_q_trap_valid     (wb_q_trap_valid     ),
    .wb_q_trap_mcause    (wb_q_trap_mcause    ),
    .wb_q_trap_pc        (wb_q_trap_pc        )
  );



  //*****************************************************************
  //
  //
  // REGISTER FILE
  //
  //
  //*****************************************************************

  regfile riscv_regfile_inst (
    .clk_i            (clk_i            ),
    .rst_i            (rst_i            ),
    .id_rs1_addr      (id_d_rs1_addr    ),
    .id_rs2_addr      (id_d_rs2_addr    ),
    .wb_q_is_rd_write (wb_q_is_rd_write ),
    .wb_rd_addr       (wb_rd_addr       ),
    .wb_rd_wdata      (wb_rd_wdata      ),
    .regfile_rs1_rdata(regfile_rs1_rdata),
    .regfile_rs2_rdata(regfile_rs2_rdata)
  );

  //*****************************************************************
  //
  //
  // CSR FILE
  //
  //
  //*****************************************************************
  csrfile csr_file_inst (
    .clk_i            (clk_i            ),
    .rst_i            (rst_i            ),
    .id_csr_addr      (id_d_csr_addr    ),
    .csrfile_rdata    (csrfile_rdata    ),
    .wb_q_valid       (wb_q_valid       ),
    .wb_q_trap_valid  (wb_q_trap_valid  ),
    .wb_q_is_csr_write(wb_q_is_csr_write),
    .wb_q_is_csr_read (wb_q_is_csr_read ),
    .wb_csr_addr      (wb_csr_addr      ),
    .wb_csr_wdata     (wb_csr_wdata     ),
    .wb_trap_pc       (wb_trap_pc       ),
    .wb_trap_mcause   (wb_trap_mcause   ),
    .ex_q_valid       (ex_q_valid       ),
    .mem_q_valid      (mem_q_valid      ),
    `ifdef RISCV_FORMAL
    .wb_csr_rmask     (wb_csr_rmask     ),
    .wb_csr_wmask     (wb_csr_wmask     ),
    `endif
    .trap_handler_addr(trap_handler_addr)
  );



  //*****************************************************************
  //
  //
  // HAZARD UNIT
  //
  //
  //*****************************************************************
  hazard_ctrl hazard_ctrl_inst (
    .id_rs1_addr          (id_d_rs1_addr        ),
    .id_rs2_addr          (id_d_rs2_addr        ),
    .ex_q_rs1_addr        (ex_q_rs1_addr        ),
    .ex_q_rs2_addr        (ex_q_rs2_addr        ),
    .ex_q_rd_addr         (ex_q_rd_addr         ),
    .mem_q_rd_addr        (mem_q_rd_addr        ),
    .wb_q_rd_addr         (wb_q_rd_addr         ),
    .ex_q_is_mem_read     (ex_q_is_mem_read     ),
    .mem_q_is_rd_write    (mem_q_is_rd_write    ),
    .wb_q_is_rd_write     (wb_q_is_rd_write     ),
    .mem_q_jump_taken     (mem_q_jump_taken     ),
    .mem_q_is_branch      (mem_q_is_branch      ),
    .mem_branch_mispredict(mem_branch_mispredict),
    .id_predict_btaken    (id_predict_btaken    ),
    .ex_q_trap_valid      (ex_q_trap_valid      ),
    .mem_q_trap_valid     (mem_q_trap_valid     ),
    .wb_q_trap_valid      (wb_q_trap_valid      ),
    .dmem_periph_req      (dmem_periph_req      ),
    .mem_done_i           (mem_done_i           ),
    .if_id_stall          (if_id_stall          ),
    .id_ex_stall          (id_ex_stall          ),
    .ex_mem_stall         (ex_mem_stall         ),
    .mem_wb_stall         (mem_wb_stall         ),
    .if_id_flush          (if_id_flush          ),
    .id_ex_flush          (id_ex_flush          ),
    .ex_mem_flush         (ex_mem_flush         ),
    .mem_wb_flush         (mem_wb_flush         ),
    .id_forward_rs1       (id_forward_rs1       ),
    .id_forward_rs2       (id_forward_rs2       ),
    .ex_forward_rs1_sel   (ex_forward_rs1_sel   ),
    .ex_forward_rs2_sel   (ex_forward_rs2_sel   )
  );

  //*****************************************************************
  //
  //
  // FORMAL VERIFICATION
  //
  //
  //*****************************************************************

`ifdef RISCV_FORMAL

  riscv_formal_if riscv_formal_if_inst (
    .clk_i                  (clk_i                  ),
    .rst_i                  (rst_i                  ),
    .mem_wb_stall           (mem_wb_stall           ),
    .trap_handler_addr      (trap_handler_addr      ),
    .wb_csr_wmask           (wb_csr_wmask           ),
    .wb_csr_rmask           (wb_csr_rmask           ),
    .wb_q_pc                (wb_q_pc                ),
    .wb_q_next_pc           (wb_q_next_pc           ),
    .wb_q_insn              (wb_q_insn              ),
    .wb_q_valid             (wb_q_valid             ),
    .wb_q_trap_valid        (wb_q_trap_valid        ),
    .wb_q_intr              (wb_q_intr              ),
    .wb_q_rs1_addr          (wb_q_rs1_addr          ),
    .wb_q_rs2_addr          (wb_q_rs2_addr          ),
    .wb_q_rs1_rdata         (wb_q_rs1_rdata         ),
    .wb_q_rs2_rdata         (wb_q_rs2_rdata         ),
    .wb_q_is_rd_write       (wb_q_is_rd_write       ),
    .wb_rd_addr             (wb_rd_addr             ),
    .wb_rd_wdata            (wb_rd_wdata            ),
    .wb_csr_addr            (wb_csr_addr            ),
    .wb_q_csr_rdata         (wb_q_csr_rdata         ),
    .wb_q_csr_wdata         (wb_q_csr_wdata         ),
    .wb_q_is_csr_read       (wb_q_is_csr_read       ),
    .wb_q_is_csr_write      (wb_q_is_csr_write      ),
    .wb_q_mem_addr          (wb_q_mem_addr          ),
    .wb_q_load_rdata        (wb_q_load_rdata        ),
    .wb_q_store_wdata       (wb_q_store_wdata       ),
    .wb_q_load_rmask        (wb_q_load_rmask        ),
    .wb_q_store_wmask       (wb_q_store_wmask       ),
    .wb_q_trap_insn         (wb_q_trap_insn         ),
    .wb_q_trap_pc           (wb_q_trap_pc           ),
    .wb_q_trap_next_pc      (wb_q_trap_next_pc      ),
    .wb_q_trap_rs1_addr     (wb_q_trap_rs1_addr     ),
    .wb_q_trap_rs2_addr     (wb_q_trap_rs2_addr     ),
    .wb_q_trap_rd_addr      (wb_q_trap_rd_addr      ),
    .wb_q_trap_rs1_rdata    (wb_q_trap_rs1_rdata    ),
    .wb_q_trap_rs2_rdata    (wb_q_trap_rs2_rdata    ),
    .wb_q_trap_rd_wdata     (wb_q_trap_rd_wdata     ),
    .rvfi_valid             (rvfi_valid             ),
    .rvfi_order             (rvfi_order             ),
    .rvfi_insn              (rvfi_insn              ),
    .rvfi_trap              (rvfi_trap              ),
    .rvfi_halt              (rvfi_halt              ),
    .rvfi_intr              (rvfi_intr              ),
    .rvfi_mode              (rvfi_mode              ),
    .rvfi_ixl               (rvfi_ixl               ),
    .rvfi_rs1_addr          (rvfi_rs1_addr          ),
    .rvfi_rs2_addr          (rvfi_rs2_addr          ),
    .rvfi_rs1_rdata         (rvfi_rs1_rdata         ),
    .rvfi_rs2_rdata         (rvfi_rs2_rdata         ),
    .rvfi_rd_addr           (rvfi_rd_addr           ),
    .rvfi_rd_wdata          (rvfi_rd_wdata          ),
    .rvfi_pc_rdata          (rvfi_pc_rdata          ),
    .rvfi_pc_wdata          (rvfi_pc_wdata          ),
    .rvfi_mem_addr          (rvfi_mem_addr          ),
    .rvfi_mem_rdata         (rvfi_mem_rdata         ),
    .rvfi_mem_wdata         (rvfi_mem_wdata         ),
    .rvfi_mem_rmask         (rvfi_mem_rmask         ),
    .rvfi_mem_wmask         (rvfi_mem_wmask         ),
    .rvfi_csr_mcycle_rdata  (rvfi_csr_mcycle_rdata  ),
    .rvfi_csr_mcycle_wdata  (rvfi_csr_mcycle_wdata  ),
    .rvfi_csr_mcycle_rmask  (rvfi_csr_mcycle_rmask  ),
    .rvfi_csr_mcycle_wmask  (rvfi_csr_mcycle_wmask  ),
    .rvfi_csr_minstret_rdata(rvfi_csr_minstret_rdata),
    .rvfi_csr_minstret_wdata(rvfi_csr_minstret_wdata),
    .rvfi_csr_minstret_rmask(rvfi_csr_minstret_rmask),
    .rvfi_csr_minstret_wmask(rvfi_csr_minstret_wmask),
    .rvfi_csr_mcause_rdata  (rvfi_csr_mcause_rdata  ),
    .rvfi_csr_mcause_wdata  (rvfi_csr_mcause_wdata  ),
    .rvfi_csr_mcause_rmask  (rvfi_csr_mcause_rmask  ),
    .rvfi_csr_mcause_wmask  (rvfi_csr_mcause_wmask  ),
    .rvfi_csr_mtvec_rdata   (rvfi_csr_mtvec_rdata   ),
    .rvfi_csr_mtvec_wdata   (rvfi_csr_mtvec_wdata   ),
    .rvfi_csr_mtvec_rmask   (rvfi_csr_mtvec_rmask   ),
    .rvfi_csr_mtvec_wmask   (rvfi_csr_mtvec_wmask   ),
    .rvfi_csr_mepc_rdata    (rvfi_csr_mepc_rdata    ),
    .rvfi_csr_mepc_wdata    (rvfi_csr_mepc_wdata    ),
    .rvfi_csr_mepc_rmask    (rvfi_csr_mepc_rmask    ),
    .rvfi_csr_mepc_wmask    (rvfi_csr_mepc_wmask    )
  );
`endif


endmodule
