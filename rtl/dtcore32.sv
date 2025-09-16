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


module dtcore32 (
    input  logic        clk_i,
    input  logic        rst_i,
`ifdef RISCV_FORMAL
    output logic        rvfi_valid,
    output logic [63:0] rvfi_order,
    output logic [31:0] rvfi_insn,
    output logic        rvfi_trap,
    output logic        rvfi_halt,
    output logic        rvfi_intr,
    output logic [ 1:0] rvfi_mode,
    output logic [ 1:0] rvfi_ixl,
    output logic [ 4:0] rvfi_rs1_addr,
    output logic [ 4:0] rvfi_rs2_addr,
    output logic [31:0] rvfi_rs1_rdata,
    output logic [31:0] rvfi_rs2_rdata,
    output logic [ 4:0] rvfi_rd_addr,
    output logic [31:0] rvfi_rd_wdata,
    output logic [31:0] rvfi_pc_rdata,
    output logic [31:0] rvfi_pc_wdata,
    output logic [31:0] rvfi_mem_addr,
    output logic [ 3:0] rvfi_mem_rmask,
    output logic [ 3:0] rvfi_mem_wmask,
    output logic [31:0] rvfi_mem_rdata,
    output logic [31:0] rvfi_mem_wdata,
    output logic [63:0] rvfi_csr_mcycle_rmask,
    output logic [63:0] rvfi_csr_mcycle_wmask,
    output logic [63:0] rvfi_csr_mcycle_rdata,
    output logic [63:0] rvfi_csr_mcycle_wdata,
    output logic [63:0] rvfi_csr_minstret_rmask,
    output logic [63:0] rvfi_csr_minstret_wmask,
    output logic [63:0] rvfi_csr_minstret_rdata,
    output logic [63:0] rvfi_csr_minstret_wdata,
    output logic [31:0] rvfi_csr_mcause_rmask,
    output logic [31:0] rvfi_csr_mcause_wmask,
    output logic [31:0] rvfi_csr_mcause_rdata,
    output logic [31:0] rvfi_csr_mcause_wdata,
    output logic [31:0] rvfi_csr_mepc_rmask,
    output logic [31:0] rvfi_csr_mepc_wmask,
    output logic [31:0] rvfi_csr_mepc_rdata,
    output logic [31:0] rvfi_csr_mepc_wdata,
    output logic [31:0] rvfi_csr_mtvec_rmask,
    output logic [31:0] rvfi_csr_mtvec_wmask,
    output logic [31:0] rvfi_csr_mtvec_rdata,
    output logic [31:0] rvfi_csr_mtvec_wdata,
`endif
    // to instruction memory interface
    input  logic [31:0] imem_rdata_i,
    output logic [31:0] imem_addr_o,

    // to data memory and peripheral interface
    input logic [31:0] mem_rdata_i,
    input logic mem_done_i,
    output logic mem_valid_o,
    output logic mem_wen_o,
    output logic [31:0] mem_addr_o,
    output logic [31:0] mem_wdata_o,
    output logic [3:0] mem_strb_o

  );
import params_pkg::*;
  localparam RESET_PC = 32'd0;

  logic   if_id_stall;
  logic   if_id_flush;
  if_id_t if_pipeline_d;
  if_id_t id_pipeline_q;
  localparam if_id_t IF_ID_RESET = '{default: 0, insn: NOP_INSTRUCTION};

  logic   id_ex_stall;
  logic   id_ex_flush;
  id_ex_t id_pipeline_d;
  id_ex_t ex_pipeline_q;
  localparam id_ex_t ID_EX_RESET = reset_id_ex();

  logic ex_mem_stall;
  logic ex_mem_flush;
  ex_mem_t ex_pipeline_d;
  ex_mem_t mem_pipeline_q;
  localparam ex_mem_t EX_MEM_RESET = reset_ex_mem();

  logic mem_wb_stall;
  logic mem_wb_flush;
  mem_wb_t mem_pipeline_d;
  mem_wb_t wb_pipeline_q;
  localparam mem_wb_t MEM_WB_RESET = reset_mem_wb();


`ifdef RISCV_FORMAL

  logic [31:0] wb_csr_rmask;
  logic [31:0] wb_csr_wmask;
`endif
  // if stage signals;
  logic [31:0] next_pc;
  logic [31:0] trap_handler_addr_q;
  logic [31:0] imem_addr_q;
  logic imem_rdata_valid;
  logic imem_buf_valid;
  logic [31:0] if_insn_buf;
  logic [31:0] if_buf_pc;
  // branch prediction logic
  logic [31:0] if_branch_offset;
  logic if_is_branch;
  logic if_predict_btaken;
  // id stage signals
  logic id_forward_a;
  logic id_forward_b;
  logic [31:0] id_insn;
  logic [11:0] id_csr_addr;
  logic [31:0] id_imm_ext;
  logic [4:0] id_rd_addr;
  alu_control_t id_alu_control;
  logic [6:0] id_op;
  logic [2:0] id_funct3;
  logic id_funct7b5;
  logic [6:0] id_funct7;
  logic [11:0] id_funct12;
  logic id_rtype_alt;
  logic id_itype_alt;
  imm_ext_op_t id_imm_ext_op;
  alu_a_sel_t id_alu_a_sel;
  alu_b_sel_t id_alu_b_sel;
  pc_alu_sel_t id_pc_alu_sel;
  csr_bitmask_sel_t id_csr_bitmask_sel;
  logic [4:0] id_rs1_addr;
  logic [4:0] id_rs2_addr;
  logic [31:0] regfile_rs1_rdata;
  logic [31:0] regfile_rs2_rdata;
  logic [31:0] csrfile_rdata;
  logic id_illegal_instr_trap;
  logic id_ecall_m_trap;
  logic id_breakpoint_trap;
  logic id_is_branch;
     logic id_is_jump;
     logic id_is_csr_write;
     logic id_is_csr_read;
     logic id_is_rd_write;
     logic id_is_rs1_read;
     logic id_is_rs2_read;
     logic id_is_mem_write;
     logic id_is_mem_read;
    logic id_is_jal;
     logic id_is_jalr;
     logic id_is_memsize_b;
     logic id_is_memsize_bu;
     logic id_is_memsize_h;
     logic id_is_memsize_hu;
     logic id_is_memsize_w;
     logic id_csr_op_rw;
     logic id_csr_op_clear;
     logic id_csr_op_set;

  // ex stage signal
  logic [2:0] ex_forward_a_sel;
  logic [2:0] ex_forward_b_sel;
  logic [31:0] ex_jaddr;
  logic ex_jump_taken;
  logic [31:0] ex_rs1_rdata;
  logic [31:0] ex_rs2_rdata;
  logic [31:0] ex_csr_bitmask;
  logic [31:0] ex_csr_wdata;
  logic [31:0] ex_src_a;
  logic [31:0] ex_src_b;
  logic [31:0] ex_pc_base;
  logic ex_branch_cond;
  logic ex_misaligned_jump;
  logic [31:0] ex_alu_result;

  //mem stage
  logic           misaligned_load;
  logic           misaligned_store;
  logic    [ 3:0] mem_wstrb;
  logic    [ 3:0] mem_rstrb;
  logic           dmem_periph_req;
  logic [31:0] mem_load_rdata;
  logic mem_btaken_mispredict;
  logic mem_bntaken_mispredict;
  logic mem_branch_mispredict;
  // writeback stage
  logic [ 4:0] wb_rd_addr;
  logic [11:0] wb_csr_addr;
  logic [31:0] wb_rd_wdata;
  logic [31:0] wb_csr_wdata;
  logic [31:0] wb_trap_mcause;
  logic [31:0] wb_trap_pc;
  //*****************************************************************
  //
  //
  // INSTRUCTION FETCH STAGE
  //
  //
  //*****************************************************************

  // On a trap, the next pc is the trap handler address,
  // else if a jump or branch, next pc is the specified jump/branch address
  // else next pc is the previous pc incremented by 4

  // send read address to the instruction memory
  always_ff @(posedge clk_i)
  begin
    if (rst_i)
    begin
      imem_addr_o <= RESET_PC;
      imem_rdata_valid <= 0;
    end
    else if (if_id_flush) begin
      imem_addr_o <= next_pc;
      imem_rdata_valid <= 0;
    end
    else if (!if_id_stall)
    begin
      imem_addr_o <= next_pc;
      imem_rdata_valid <= 1;
    end
  end


  // registers imem address to stay cycle aligned with imem rdata
  // imem reads have 1 cycle latency
  always_ff @(posedge clk_i)
  begin
    if (rst_i) begin
      imem_addr_q <= RESET_PC;
    end else begin
      imem_addr_q <= imem_addr_o;
    end
  end

  // buffer
  always_ff @(posedge clk_i)
  begin
    if (rst_i)
    begin
      imem_buf_valid <= 0;
    end
    else if (if_id_flush) begin
      imem_buf_valid <= 0;
    end
    else if (!if_id_stall)
    begin
      imem_buf_valid <= 0;
    end
    // When entering a stall, buffer the instruction memory read data.
    // When first leaving a stall, use the buffered data instead. This
    // is to avoid losing instruction data when entering a stall.
    else if (if_id_stall && !imem_buf_valid)
    begin
      if_insn_buf <= imem_rdata_i;
      imem_buf_valid <= 1;
      if_buf_pc <= imem_addr_q;
    end
  end

  always_comb
  begin
    // jump to trap handler if a trap instruction commits
    // else if a branch taken and mispredicted jump to mem.pc + 4
    // else if a branch not taken and mispredicted OR a jump instruction
    // jump to mem.jaddr
    // else if a branch taken is predicted jump to that address
    // else increment pc by 4
    next_pc = wb_pipeline_q.trap_valid ? trap_handler_addr_q :
                mem_btaken_mispredict ? mem_pipeline_q.pc + 4 :
                (mem_bntaken_mispredict
                || (mem_pipeline_q.jump_taken && !mem_pipeline_q.is_branch)) ? mem_pipeline_q.jaddr:
                if_predict_btaken ? imem_addr_o + if_branch_offset :
                imem_addr_o + 4;
    if_pipeline_d.pc = imem_buf_valid ? if_buf_pc : imem_addr_q;
    if_pipeline_d.pc_plus_4 = if_pipeline_d.pc + 4;
    if_pipeline_d.insn = imem_buf_valid ? if_insn_buf : imem_rdata_i;;
    if_pipeline_d.valid = imem_rdata_valid;
    if_pipeline_d.branch_predict = if_predict_btaken;
  end


  //*****************************************************************
  //
  //
  // BRANCH PREDICTION
  //
  //
  //*****************************************************************
  
  // decode fetched instruction early for branch prediction
  assign if_is_branch = (if_pipeline_d.insn[6:0] == 7'h33);
  assign if_branch_offset = {{20{if_pipeline_d.insn[31]}}, if_pipeline_d.insn[7], if_pipeline_d.insn[30:25], if_pipeline_d.insn[11:8], 1'b0};

  gshare  gshare_inst (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .pc_lsb10_i(if_pipeline_d.pc[11:2]),
    .branch_taken_i(mem_pipeline_q.jump_taken),
    .branch_result_valid_i(mem_pipeline_q.is_branch),
    .branch_predict_valid_i(if_is_branch),
    .branch_predict_o(if_predict_btaken)
  );

`ifdef RISCV_FORMAL
  logic if_intr_d;
  logic if_intr_q;
  logic if_intr_qq;
  always_ff @(posedge clk_i)
  begin
    if (rst_i)
    begin
      if_intr_q <= 0;
      if_intr_qq <= 0;
    end
    else if (if_id_flush)
    begin
      if_intr_q <= 0;
      if_intr_qq <= 0;
    end
    else if (!if_id_stall)
    begin
      if_intr_q <= if_intr_d;
      if_intr_qq <= if_intr_q;
    end
  end
  always_comb
  begin
    if_pipeline_d.intr = if_intr_qq;
    if_intr_d = wb_pipeline_q.trap_valid;
  end
`endif
  //*****************************************************************
  //
  //
  // INSTRUCTION DECODE STAGE
  //
  //
  //*****************************************************************

           decoder  decoder_inst (
    .op_i(id_op),
    .funct3_i(id_funct3),
    .funct7_i(id_funct7),
    .funct12_i(id_funct12),
    .rs1_addr_i(id_rs1_addr),
    .rd_addr_i(id_rd_addr),
    .rtype_alt_i(id_rtype_alt),
    .itype_alt_i(id_itype_alt),
    .alu_control_o(id_alu_control),
    .imm_ext_op_o(id_imm_ext_op),
    .alu_a_sel_o(id_alu_a_sel),
    .alu_b_sel_o(id_alu_b_sel),
    .pc_alu_sel_o(id_pc_alu_sel),
    .csr_bitmask_sel_o(id_csr_bitmask_sel),
    .is_branch_o(id_is_branch),
    .is_jump_o(id_is_jump),
    .is_csr_write_o(id_is_csr_write),
    .is_csr_read_o(id_is_csr_read),
    .is_rd_write_o(id_is_rd_write),
    .is_rs1_read_o(id_is_rs1_read),
    .is_rs2_read_o(id_is_rs2_read),
    .is_mem_write_o(id_is_mem_write),
    .is_mem_read_o(id_is_mem_read),
    .is_jal_o(id_is_jal),
    .is_jalr_o(id_is_jalr),
    .is_memsize_b_o(id_is_memsize_b),
    .is_memsize_bu_o(id_is_memsize_bu),
    .is_memsize_h_o(id_is_memsize_h),
    .is_memsize_hu_o(id_is_memsize_hu),
    .is_memsize_w_o(id_is_memsize_w),
    .csr_op_rw_o(id_csr_op_rw),
    .csr_op_clear_o(id_csr_op_clear),
    .csr_op_set_o(id_csr_op_set),
    .illegal_instr_trap_o(id_illegal_instr_trap),
    .ecall_m_trap_o(id_ecall_m_trap),
    .breakpoint_trap_o(id_breakpoint_trap)
  );

  extend extend_inst (
           .insn_i(id_insn),
           .imm_ext_op_i(id_imm_ext_op),
           .imm_ext_o(id_imm_ext)
         );

  // assign signals propagating to the next stage
  always_comb
  begin
    id_insn = id_pipeline_q.insn;
    id_op = id_insn[6:0];
    id_funct3 = id_insn[14:12];
    id_funct7b5 = id_insn[30];
    id_funct7 = id_insn[31:25];
    id_funct12 = id_insn[31:20];
    id_rtype_alt = id_op[5] & id_funct7b5;
    id_itype_alt = ~id_op[5] & id_funct7b5;
    id_rs1_addr = id_is_rs1_read ? id_insn[19:15] : 0;
    id_rs2_addr = id_is_rs2_read ? id_insn[24:20] : 0;
    id_rd_addr = id_insn[11:7];
    id_csr_addr = id_insn[31:20];
    // Branch and jump
    id_pipeline_d.is_branch     = id_is_branch;
    id_pipeline_d.is_jump       = id_is_jump;
    id_pipeline_d.is_jal        = id_is_jal;
    id_pipeline_d.is_jalr       = id_is_jalr;
    id_pipeline_d.branch_predict = id_pipeline_q.branch_predict;

    // CSR operations
    id_pipeline_d.is_csr_write  = id_is_csr_write;
    id_pipeline_d.is_csr_read   = id_is_csr_read;
    id_pipeline_d.csr_op_rw     = id_csr_op_rw;
    id_pipeline_d.csr_op_clear  = id_csr_op_clear;
    id_pipeline_d.csr_op_set    = id_csr_op_set;

    // Register reads/writes
    id_pipeline_d.is_rd_write   = id_is_rd_write;
    id_pipeline_d.is_rs1_read   = id_is_rs1_read;
    id_pipeline_d.is_rs2_read   = id_is_rs2_read;

    // Memory access
    id_pipeline_d.is_mem_write  = id_is_mem_write;
    id_pipeline_d.is_mem_read   = id_is_mem_read;

    // Memory size indicators
    id_pipeline_d.is_memsize_b  = id_is_memsize_b;
    id_pipeline_d.is_memsize_bu = id_is_memsize_bu;
    id_pipeline_d.is_memsize_h  = id_is_memsize_h;
    id_pipeline_d.is_memsize_hu = id_is_memsize_hu;
    id_pipeline_d.is_memsize_w  = id_is_memsize_w;

    //
    id_pipeline_d.valid           = id_pipeline_q.valid;
    id_pipeline_d.pc              = id_pipeline_q.pc;
    id_pipeline_d.pc_plus_4       = id_pipeline_q.pc_plus_4;
    id_pipeline_d.rs1_addr        = id_rs1_addr;
    id_pipeline_d.rs2_addr        = id_rs2_addr;
    id_pipeline_d.rd_addr         = id_rd_addr;
    id_pipeline_d.rs1_rdata       = id_forward_a ? wb_rd_wdata : regfile_rs1_rdata;
    id_pipeline_d.rs2_rdata       = id_forward_b ? wb_rd_wdata : regfile_rs2_rdata;
    id_pipeline_d.imm_ext         = id_imm_ext;
    id_pipeline_d.csr_addr        = id_csr_addr;
    id_pipeline_d.csr_rdata       = csrfile_rdata;
    id_pipeline_d.alu_control     = id_alu_control;
    id_pipeline_d.alu_a_sel       = id_alu_a_sel;
    id_pipeline_d.alu_b_sel       = id_alu_b_sel;
    id_pipeline_d.pc_alu_sel      = id_pc_alu_sel;
    id_pipeline_d.csr_bitmask_sel = id_csr_bitmask_sel;
    // trap info
    if (id_ecall_m_trap | id_breakpoint_trap | id_illegal_instr_trap)
    begin
      id_pipeline_d.trap_valid = 1;
      id_pipeline_d.trap_pc = id_pipeline_q.pc;
      if (id_ecall_m_trap)
      begin
        id_pipeline_d.trap_mcause = {1'd0, TRAP_CODE_ECALL_M_MODE};
      end
      else if (id_breakpoint_trap)
      begin
        id_pipeline_d.trap_mcause = {1'd0, TRAP_CODE_BREAKPOINT};
      end
      else
      begin // illegal instruction
        id_pipeline_d.trap_mcause = {1'd0, TRAP_CODE_ILLEGAL_INSTR};
      end
      
    end
    else
    begin
      id_pipeline_d.trap_valid = 0;
      id_pipeline_d.trap_mcause = 'x;
      id_pipeline_d.trap_pc = 'x;
    end
  end

`ifdef RISCV_FORMAL
  trap_info_t rvfi_id_trap;
  always_comb
  begin
    // rvfi metadata
    id_pipeline_d.insn = id_insn;
    id_pipeline_d.intr = id_pipeline_q.intr;
    id_pipeline_d.rvfi_trap_info = rvfi_id_trap;
    // trap info for rvfi
    rvfi_id_trap.insn = id_insn;
    rvfi_id_trap.pc = id_pipeline_q.pc;
    rvfi_id_trap.next_pc = 0;
    rvfi_id_trap.rs1_addr = 0;
    rvfi_id_trap.rs2_addr = 0;
    rvfi_id_trap.rd_addr = 0;
    rvfi_id_trap.rs1_rdata = 0;
    rvfi_id_trap.rs2_rdata = 0;
    rvfi_id_trap.rd_wdata = 0;
  end
`endif
  


  //*****************************************************************
  //
  //
  // INSTRUCTION EXECUTE STAGE
  //
  //
  //*****************************************************************
  
  // select rs1 read data
always_comb begin
  case (ex_forward_a_sel)
    NO_FORWARD_SEL:
      ex_rs1_rdata = ex_pipeline_q.rs1_rdata;
    FORWARD_SEL_MEM_RESULT:
      ex_rs1_rdata = mem_pipeline_q.alu_csr_result;
    FORWARD_SEL_WB_RESULT:
      ex_rs1_rdata = wb_rd_wdata;
    default:
      ex_rs1_rdata = 'x;
  endcase
end

// select input data for the first alu input
always_comb begin
  case (ex_pipeline_q.alu_a_sel)
    ALU_A_SEL_REG_DATA:
      ex_src_a = ex_rs1_rdata;
    ALU_A_SEL_PC:
      ex_src_a = ex_pipeline_q.pc;
    ALU_A_SEL_ZERO:
      ex_src_a = 0;
    default:
      ex_src_a = 'x;
  endcase
end

// select rs2 read data
always_comb begin
  case (ex_forward_b_sel)
    NO_FORWARD_SEL:
      ex_rs2_rdata = ex_pipeline_q.rs2_rdata;
    FORWARD_SEL_MEM_RESULT:
      ex_rs2_rdata = mem_pipeline_q.alu_csr_result;
    FORWARD_SEL_WB_RESULT:
      ex_rs2_rdata = wb_rd_wdata;
    default:
      ex_rs2_rdata = 'x;
  endcase
end

// select input data for the second alu input
always_comb begin
  case (ex_pipeline_q.alu_b_sel)
    ALU_B_SEL_REG_DATA:
      ex_src_b = ex_rs2_rdata;
    ALU_B_SEL_IMM:
      ex_src_b = ex_pipeline_q.imm_ext;
    default:
      ex_src_b = 'x;
  endcase
end

// select base value for pc offset
always_comb begin
  case (ex_pipeline_q.pc_alu_sel)
    PC_ALU_SEL_REG_DATA:
      ex_pc_base = ex_rs1_rdata;
    PC_ALU_SEL_PC:
      ex_pc_base = ex_pipeline_q.pc;
    default:
      ex_pc_base = 'x;
  endcase
end

// select bitmask source for csr op
always_comb begin
  case (ex_pipeline_q.csr_bitmask_sel)
    CSR_BITMASK_SEL_REG_DATA:
      ex_csr_bitmask = ex_rs1_rdata;
    CSR_BITMASK_SEL_IMM:
      ex_csr_bitmask = ex_pipeline_q.imm_ext;
    default:
      ex_csr_bitmask = 'x;
  endcase
end

// select csr result depending on op type
always_comb begin
  if (ex_pipeline_q.csr_op_rw) begin
    ex_csr_wdata = ex_csr_bitmask;
  end
  else if (ex_pipeline_q.csr_op_clear) begin
    ex_csr_wdata = (ex_pipeline_q.csr_rdata & ~ex_csr_bitmask);
  end
  else if (ex_pipeline_q.csr_op_set) begin
    ex_csr_wdata = (ex_pipeline_q.csr_rdata | ex_csr_bitmask);
  end
  else begin
    ex_csr_wdata = 'x;
  end
end
    // trap if the jump address is not word aligned
    // jump if instruction is a jump or a branch and condition is true
    // jump is delayed to the mem stage to avoid long combinational path
    assign ex_jaddr     = (ex_pipeline_q.is_jalr) ? ((ex_pc_base + ex_pipeline_q.imm_ext) & ~(1'b1)) : (ex_pc_base + ex_pipeline_q.imm_ext);
    assign ex_jump_taken = (ex_pipeline_q.is_jump | (ex_pipeline_q.is_branch & ex_branch_cond));
    assign ex_misaligned_jump = ex_jump_taken & (ex_jaddr[1] | ex_jaddr[0]);

  always_comb
  begin
    // Branch and jump
    ex_pipeline_d.is_branch     = ex_pipeline_q.is_branch;
    ex_pipeline_d.is_jump       = ex_pipeline_q.is_jump;
    ex_pipeline_d.is_jal = ex_pipeline_q.is_jal;
    ex_pipeline_d.is_jalr       = ex_pipeline_q.is_jalr;
    ex_pipeline_d.branch_predict = ex_pipeline_q.branch_predict;

    // CSR operations
    ex_pipeline_d.is_csr_write  = ex_pipeline_q.is_csr_write;
    ex_pipeline_d.is_csr_read   = ex_pipeline_q.is_csr_read;

    // Register writes
    if (ex_misaligned_jump)
      ex_pipeline_d.is_rd_write = 0;
    else
      ex_pipeline_d.is_rd_write = ex_pipeline_q.is_rd_write;

    // Memory access
    ex_pipeline_d.is_mem_write  = ex_pipeline_q.is_mem_write;
    ex_pipeline_d.is_mem_read   = ex_pipeline_q.is_mem_read;

    // Memory size indicators
    ex_pipeline_d.is_memsize_b  = ex_pipeline_q.is_memsize_b;
    ex_pipeline_d.is_memsize_bu = ex_pipeline_q.is_memsize_bu;
    ex_pipeline_d.is_memsize_h  = ex_pipeline_q.is_memsize_h;
    ex_pipeline_d.is_memsize_hu = ex_pipeline_q.is_memsize_hu;
    ex_pipeline_d.is_memsize_w  = ex_pipeline_q.is_memsize_w;

    // pipeline
    ex_pipeline_d.valid          = ex_pipeline_q.valid;
    ex_pipeline_d.pc             = ex_pipeline_q.pc;
    ex_pipeline_d.pc_plus_4      = ex_pipeline_q.pc_plus_4;
    ex_pipeline_d.rd_addr        = ex_pipeline_q.rd_addr;
    ex_pipeline_d.csr_addr       = ex_pipeline_q.csr_addr;
    ex_pipeline_d.csr_wdata      = ex_csr_wdata;
    ex_pipeline_d.store_wdata    = ex_rs2_rdata;
    ex_pipeline_d.alu_csr_result = (ex_pipeline_q.is_csr_read) ? ex_pipeline_q.csr_rdata : ex_alu_result;
    ex_pipeline_d.jaddr = ex_jaddr;
    ex_pipeline_d.jump_taken = ex_jump_taken;
    // traps
    if (ex_pipeline_q.trap_valid)
    begin
      ex_pipeline_d.trap_valid = 1;
      ex_pipeline_d.trap_mcause = ex_pipeline_q.trap_mcause;
      ex_pipeline_d.trap_pc = ex_pipeline_q.trap_pc;
    end
    else if (ex_misaligned_jump)
    begin
      ex_pipeline_d.trap_valid = 1;
      ex_pipeline_d.trap_mcause = {1'b0, TRAP_CODE_INSTR_ADDR_MISALIGNED};
      ex_pipeline_d.trap_pc = ex_pipeline_q.pc;
    end
    else
    begin
      ex_pipeline_d.trap_valid = 0;
      ex_pipeline_d.trap_mcause = 'x;
      ex_pipeline_d.trap_pc = 'x;
    end
  end

  alu alu_inst (
        .a_i(ex_src_a),
        .b_i(ex_src_b),
        .control_i(ex_pipeline_q.alu_control),
        .branch_cond_o(ex_branch_cond),
        .result_o(ex_alu_result)
      );

`ifdef RISCV_FORMAL

  trap_info_t rvfi_ex_trap_info;
  logic [31:0] ex_next_pc;
  assign ex_next_pc = (ex_jump_taken) ? ex_jaddr : ex_pipeline_q.pc_plus_4;
  always_comb
  begin
    // additional stage info
    ex_pipeline_d.next_pc        = ex_next_pc;
    ex_pipeline_d.insn           = ex_pipeline_q.insn;
    ex_pipeline_d.intr           = ex_pipeline_q.intr;
    ex_pipeline_d.rs1_addr       = ex_pipeline_q.rs1_addr;
    ex_pipeline_d.rs2_addr       = ex_pipeline_q.rs2_addr;
    ex_pipeline_d.rs1_rdata      = ex_rs1_rdata;
    ex_pipeline_d.rs2_rdata      = ex_rs2_rdata;
    ex_pipeline_d.csr_rdata = ex_pipeline_q.csr_rdata;
    ex_pipeline_d.rvfi_trap_info = rvfi_ex_trap_info;
    // additional trap info
    rvfi_ex_trap_info.insn = ex_pipeline_q.insn;
    rvfi_ex_trap_info.pc = ex_pipeline_q.pc;
    rvfi_ex_trap_info.next_pc = ex_next_pc;
    rvfi_ex_trap_info.rs1_addr = ex_pipeline_q.rs1_addr;
    rvfi_ex_trap_info.rs2_addr = ex_pipeline_q.rs2_addr;
    rvfi_ex_trap_info.rd_addr = ex_pipeline_q.rd_addr;
    rvfi_ex_trap_info.rs1_rdata = ex_src_a;
    rvfi_ex_trap_info.rs2_rdata = ex_rs2_rdata;
    rvfi_ex_trap_info.rd_wdata = 0;
    if (ex_pipeline_q.trap_valid) // if trap from previous stage save it instead
    begin
      rvfi_ex_trap_info = ex_pipeline_q.rvfi_trap_info;
    end
  end
`endif
  //*****************************************************************
  //
  //
  // DATA MEMORY STAGE
  //
  //
  //*****************************************************************
     logic [4:0] load_size_onehot;
     logic [2:0] store_size_onehot;
     assign mem_btaken_mispredict = (mem_pipeline_q.is_branch && !mem_pipeline_q.jump_taken && mem_pipeline_q.branch_predict);
     assign mem_bntaken_mispredict = (mem_pipeline_q.is_branch && mem_pipeline_q.jump_taken && !mem_pipeline_q.branch_predict);
     assign mem_branch_mispredict = mem_btaken_mispredict || mem_bntaken_mispredict;
     assign load_size_onehot = !mem_pipeline_q.is_mem_read ? '0 : 
     {
      mem_pipeline_q.is_memsize_w, 
      mem_pipeline_q.is_memsize_hu,
      mem_pipeline_q.is_memsize_h, 
      mem_pipeline_q.is_memsize_bu, 
      mem_pipeline_q.is_memsize_b
    };
    assign store_size_onehot = !mem_pipeline_q.is_mem_write ? '0 : 
    {
      mem_pipeline_q.is_memsize_w, 
      mem_pipeline_q.is_memsize_h, 
      mem_pipeline_q.is_memsize_b
    };

  pulse_generator pulse_generator_inst (
                    .clk_i(clk_i),
                    .rst_i(rst_i),
                    .en_i(dmem_periph_req && !mem_done_i),
                    .pulse_o(mem_valid_o)
                  );

  load_unit  load_unit_inst (
               .mem_size_onehot(load_size_onehot),
               .raddr_lower2_i(mem_pipeline_q.alu_csr_result[1:0]),
               .rdata_unformatted_i(mem_rdata_i),
               .misaligned_load_o(misaligned_load),
               .rstrb_o(mem_rstrb),
               .rdata_o(mem_load_rdata)
             );

  store_unit  store_unit_inst (
                .store_size_onehot_i(store_size_onehot),
                .waddr_lower2_i(mem_pipeline_q.alu_csr_result[1:0]),
                .wdata_unformatted_i(mem_pipeline_q.store_wdata),
                .misaligned_store_o(misaligned_store),
                .wstrb_o(mem_wstrb),
                .wdata_o(mem_wdata_o)
              );

  always_comb
  begin
    // memory interface local signals
    dmem_periph_req = (mem_pipeline_q.is_mem_write || mem_pipeline_q.is_mem_read) && (!misaligned_load || !misaligned_store);
    mem_wen_o = mem_pipeline_q.is_mem_write;
    mem_addr_o = mem_pipeline_q.alu_csr_result;
    mem_strb_o = mem_wen_o ? mem_wstrb : mem_rstrb;

    // pipeline
    mem_pipeline_d.valid       = mem_pipeline_q.valid;
    mem_pipeline_d.is_csr_write = mem_pipeline_q.is_csr_write;
    mem_pipeline_d.is_csr_read  = mem_pipeline_q.is_csr_read;
    mem_pipeline_d.is_rd_write  =  misaligned_load ? 0 : mem_pipeline_q.is_rd_write;
    mem_pipeline_d.rd_addr     = mem_pipeline_q.rd_addr;

    if (mem_pipeline_q.is_jalr | mem_pipeline_q.is_jal)  // is a jal or jalr
      mem_pipeline_d.rd_wdata  = mem_pipeline_q.pc_plus_4;
    else if (mem_pipeline_q.is_mem_read)  // is a load instruction
      mem_pipeline_d.rd_wdata  = mem_load_rdata;
    else  // else
      mem_pipeline_d.rd_wdata  = mem_pipeline_q.alu_csr_result;
  
    mem_pipeline_d.csr_addr    = mem_pipeline_q.csr_addr;
    mem_pipeline_d.csr_wdata   = mem_pipeline_q.csr_wdata;
    // traps
    if (mem_pipeline_q.trap_valid)
    begin
      mem_pipeline_d.trap_valid = 1;
      mem_pipeline_d.trap_mcause = mem_pipeline_q.trap_mcause;
      mem_pipeline_d.trap_pc = mem_pipeline_q.trap_pc;
    end
    else if (misaligned_store)
    begin
      mem_pipeline_d.trap_valid = 1;
      mem_pipeline_d.trap_mcause = {1'b0, TRAP_CODE_STORE_ADDR_MISALIGNED};
      mem_pipeline_d.trap_pc = mem_pipeline_q.pc;
      
    end
    else if (misaligned_load)
    begin
      mem_pipeline_d.trap_valid = 1;
      mem_pipeline_d.trap_mcause = {1'b0, TRAP_CODE_LOAD_ADDR_MISALIGNED};
      mem_pipeline_d.trap_pc = mem_pipeline_q.pc;
    end
    else
    begin
      mem_pipeline_d.trap_valid  = 0;
      mem_pipeline_d.trap_mcause = 'x;
      mem_pipeline_d.trap_pc     = 'x;
    end
  end

`ifdef RISCV_FORMAL
  trap_info_t mem_trap;
  always_comb
  begin
    // rvfi
    mem_pipeline_d.pc             = mem_pipeline_q.pc;
    // next pc changes on a branch mispredict
    mem_pipeline_d.next_pc        = mem_btaken_mispredict  ? (mem_pipeline_q.pc + 4) :
                                    mem_bntaken_mispredict ? (mem_pipeline_q.jaddr) :
                                    mem_pipeline_q.next_pc;
    mem_pipeline_d.insn           = mem_pipeline_q.insn;
    mem_pipeline_d.intr           = mem_pipeline_q.intr;
    mem_pipeline_d.pc_plus_4 = mem_pipeline_q.pc_plus_4;
    mem_pipeline_d.rs1_addr       = mem_pipeline_q.rs1_addr;
    mem_pipeline_d.rs2_addr       = mem_pipeline_q.rs2_addr;
    mem_pipeline_d.rs1_rdata      = mem_pipeline_q.rs1_rdata;
    mem_pipeline_d.rs2_rdata      = mem_pipeline_q.rs2_rdata;
    mem_pipeline_d.mem_addr     = mem_addr_o;
    mem_pipeline_d.load_rmask     = mem_rstrb;
    mem_pipeline_d.store_wmask    = mem_wstrb;
    mem_pipeline_d.store_wdata    = mem_wdata_o;
    mem_pipeline_d.rvfi_trap_info = mem_trap;
    // trap
    mem_trap.insn                 = mem_pipeline_q.insn;
    mem_trap.pc                   = mem_pipeline_q.pc;
    mem_trap.next_pc              = mem_pipeline_q.next_pc;
    mem_pipeline_d.csr_rdata      = mem_pipeline_q.csr_rdata;
    mem_trap.rs1_addr             = mem_pipeline_q.rs1_addr;
    mem_trap.rs2_addr             = mem_pipeline_q.rs2_addr;
    mem_trap.rd_addr              = mem_pipeline_q.rd_addr;
    mem_pipeline_d.load_rdata     = mem_load_rdata;
    mem_trap.rs1_rdata            = mem_pipeline_q.rs1_rdata;
    mem_trap.rs2_rdata            = mem_pipeline_q.rs2_rdata;
    mem_trap.rd_wdata             = 0;
    if (mem_pipeline_q.trap_valid)
    begin
      mem_trap = mem_pipeline_q.rvfi_trap_info;
    end
  end
`endif

  //*****************************************************************
  //
  //
  // WRITEBACK STAGE
  //
  //
  //*****************************************************************


  always_comb
  begin
    wb_trap_mcause = wb_pipeline_q.trap_mcause;
    wb_trap_pc = wb_pipeline_q.trap_pc;
    wb_rd_addr = wb_pipeline_q.rd_addr;
    wb_rd_wdata = wb_pipeline_q.rd_wdata;
    wb_csr_addr = wb_pipeline_q.csr_addr;
    wb_csr_wdata = wb_pipeline_q.csr_wdata;
  end

  //*****************************************************************
  //
  //
  // PIPELINE REGISTERS
  //
  //
  //*****************************************************************
  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      id_pipeline_q <= IF_ID_RESET;
    end else if (if_id_flush) begin
      id_pipeline_q.valid <= 0;
      id_pipeline_q.insn <= NOP_INSTRUCTION;
    end else if (!if_id_stall) begin
      id_pipeline_q <= if_pipeline_d;
      id_pipeline_q.insn <= imem_rdata_valid ? if_pipeline_d.insn : NOP_INSTRUCTION;
    end
  end
  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      ex_pipeline_q <= ID_EX_RESET;
    end else if (id_ex_flush) begin
      ex_pipeline_q.is_branch <= 0;
      ex_pipeline_q.is_jump <= 0;
      ex_pipeline_q.is_csr_write <= 0;
      ex_pipeline_q.is_csr_read <= 0;
      ex_pipeline_q.is_rd_write <= 0;
      ex_pipeline_q.is_rs1_read <= 0;
      ex_pipeline_q.is_rs2_read <= 0;
      ex_pipeline_q.is_mem_write <= 0;
      ex_pipeline_q.is_mem_read <= 0;
      ex_pipeline_q.valid <= 0;
      ex_pipeline_q.trap_valid <= 0;
    end else if (!id_ex_stall) begin
      ex_pipeline_q <= id_pipeline_d;
    end
  end

  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      mem_pipeline_q <= EX_MEM_RESET;
    end else if (ex_mem_flush) begin
      mem_pipeline_q.is_branch <= 0;
      mem_pipeline_q.is_csr_write <= 0;
      mem_pipeline_q.is_csr_read <= 0;
      mem_pipeline_q.is_rd_write <= 0;
      mem_pipeline_q.is_mem_write <= 0;
      mem_pipeline_q.is_mem_read <= 0;
      mem_pipeline_q.valid <= 0;
      mem_pipeline_q.trap_valid <= 0;
      mem_pipeline_q.jump_taken <= 0;

    end else if (!ex_mem_stall) begin
      mem_pipeline_q <= ex_pipeline_d;
    end
  end

  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      wb_pipeline_q <= MEM_WB_RESET;
    end else if (mem_wb_flush) begin
      wb_pipeline_q.is_csr_write <= 0;
      wb_pipeline_q.is_csr_read <= 0;
      wb_pipeline_q.is_rd_write <= 0;
      wb_pipeline_q.valid <= 0;
      wb_pipeline_q.trap_valid <= 0;
    end else if (!mem_wb_stall) begin
      wb_pipeline_q <= mem_pipeline_d;
    end
  end
  //*****************************************************************
  //
  //
  // ADDITIONAL MODULES
  //
  //
  //*****************************************************************
  csrfile  csrfile_inst (
             .clk_i(clk_i),
             .rst_i(rst_i),
`ifdef RISCV_FORMAL
             .wb_csr_rmask_o(wb_csr_rmask),
             .wb_csr_wmask_o(wb_csr_wmask),
             .wb_rd_addr_i(wb_rd_addr),
`endif
             .write_en_i(wb_pipeline_q.is_csr_write),
             .read_en_i(wb_pipeline_q.is_csr_read),
             .id_csr_raddr_i(id_csr_addr),
             .id_csr_rdata_o(csrfile_rdata),
             
             .wb_csr_waddr_i(wb_csr_addr),
             .wb_csr_wdata_i(wb_csr_wdata),
             .wb_valid_i(wb_pipeline_q.valid),
             .ex_valid_i(ex_pipeline_q.valid),
             .mem_valid_i(mem_pipeline_q.valid),
             .wb_trap_valid_i(wb_pipeline_q.trap_valid),
             .wb_trap_pc_i(wb_trap_pc),
             .wb_trap_mcause_i(wb_trap_mcause),
             .trap_handler_addr_q(trap_handler_addr_q),
             .external_irq_pending_i()
           );
  regfile  regfile_inst (
             .clk_i(clk_i),
             .rst_i(rst_i),
             .write_en_i(wb_pipeline_q.is_rd_write),
             .rs1_addr_i(id_rs1_addr),
             .rs2_addr_i(id_rs2_addr),
             .rd_addr_i(wb_rd_addr),
             .reg_wr_data_i(wb_rd_wdata),
             .rs1_rdata_o(regfile_rs1_rdata),
             .rs2_rdata_o(regfile_rs2_rdata)
           );

           hazard_unit  hazard_unit_inst (
    .mem_is_rd_write_i(mem_pipeline_q.is_rd_write),
    .wb_is_rd_write_i(wb_pipeline_q.is_rd_write),
    .id_rs1_addr_i(id_rs1_addr),
    .id_rs2_addr_i(id_rs2_addr),
    .ex_rs1_addr_i(ex_pipeline_q.rs1_addr),
    .ex_rs2_addr_i(ex_pipeline_q.rs2_addr),
    .ex_rd_addr_i(ex_pipeline_q.rd_addr),
    .mem_rd_addr_i(mem_pipeline_q.rd_addr),
    .wb_rd_addr_i(wb_pipeline_q.rd_addr),
    .id_forward_a_o(id_forward_a),
    .id_forward_b_o(id_forward_b),
    .ex_forward_a_sel_o(ex_forward_a_sel),
    .ex_forward_b_sel_o(ex_forward_b_sel),
    .mem_jump_taken_i(mem_pipeline_q.jump_taken),
    .mem_branch_mispredict_i(mem_branch_mispredict),
    .mem_is_branch_i(mem_pipeline_q.is_branch),
    .mem_req_i(dmem_periph_req),
    .mem_done_i(mem_done_i),
    .ex_is_mem_read_i(ex_pipeline_q.is_mem_read),
    .if_id_flush_o(if_id_flush),
    .id_ex_flush_o(id_ex_flush),
    .ex_mem_flush_o(ex_mem_flush),
    .mem_wb_flush_o(mem_wb_flush),
    .if_id_stall_o(if_id_stall),
    .id_ex_stall_o(id_ex_stall),
    .ex_mem_stall_o(ex_mem_stall),
    .mem_wb_stall_o(mem_wb_stall),
    .ex_trap_valid_i(ex_pipeline_q.trap_valid),
    .mem_trap_valid_i(mem_pipeline_q.trap_valid),
    .wb_trap_valid_i(wb_pipeline_q.trap_valid)
  );
  // instruction memory interface
  // data memory interface

  //////////////////////////////////////
  //
  //  FORMAL VERIFICATION
  //
  //
  ///////////////////////////////////////

`ifdef RISCV_FORMAL

  rvfi_t wb_rvfi;
  logic  is_csr_mstatus;
  logic  is_csr_misa;
  logic  is_csr_mie;
  logic  is_csr_mtvec;
  logic  is_csr_mscratch;
  logic  is_csr_mepc;
  logic  is_csr_mcause;
  logic  is_csr_mtval;
  logic  is_csr_mip;
  logic  is_csr_mcycle;
  logic  is_csr_mcycleh;
  logic  is_csr_minstret;
  logic  is_csr_minstreth;
  logic  is_csr_mvendorid;
  logic  is_csr_marchid;
  logic  is_csr_mimpid;
  logic  is_csr_mhartid;
  logic  is_csr_mconfigptr;
  logic  rvfi_valid_next;
  assign rvfi_valid_next = mem_wb_stall ? 0 : wb_rvfi.valid;

  always_comb
  begin
    // PC + instruction flow
    wb_rvfi.pc_rdata  = wb_pipeline_q.pc;
    wb_rvfi.pc_wdata  = wb_pipeline_q.next_pc;
    wb_rvfi.insn      = wb_pipeline_q.insn;
    wb_rvfi.valid     = wb_pipeline_q.valid;
    wb_rvfi.trap_valid = wb_pipeline_q.trap_valid;
    wb_rvfi.intr      = wb_pipeline_q.intr;

    // Register file signals
    wb_rvfi.rs1_addr  = wb_pipeline_q.rs1_addr;
    wb_rvfi.rs2_addr  = wb_pipeline_q.rs2_addr;
    wb_rvfi.rd_addr   = wb_pipeline_q.is_rd_write ? wb_rd_addr : 0;
    wb_rvfi.rs1_rdata = wb_pipeline_q.rs1_rdata;
    wb_rvfi.rs2_rdata = wb_pipeline_q.rs2_rdata;
    wb_rvfi.rd_wdata  = wb_pipeline_q.is_rd_write ? wb_rd_wdata : 0;

    // CSR signals
    wb_rvfi.csr_addr  = wb_csr_addr;
    wb_rvfi.csr_wdata = wb_pipeline_q.csr_wdata;
    wb_rvfi.csr_wmask = wb_pipeline_q.is_csr_write ? wb_csr_wmask : 0;
    wb_rvfi.csr_rdata = wb_pipeline_q.csr_rdata;
    wb_rvfi.csr_rmask = wb_pipeline_q.is_csr_read ? wb_csr_rmask : 0;

    // Memory interface
    wb_rvfi.mem_addr  = wb_pipeline_q.mem_addr;
    wb_rvfi.mem_rmask = wb_pipeline_q.load_rmask;
    wb_rvfi.mem_rdata = wb_pipeline_q.load_rdata;
    wb_rvfi.mem_wmask = wb_pipeline_q.store_wmask;
    wb_rvfi.mem_wdata = wb_pipeline_q.store_wdata;

    // Trap info
    wb_rvfi.rvfi_trap_info      = wb_pipeline_q.rvfi_trap_info;
  end


  always_comb
  begin
    is_csr_mstatus = 0;
    is_csr_misa = 0;
    is_csr_mie = 0;
    is_csr_mtvec = 0;
    is_csr_mscratch = 0;
    is_csr_mepc = 0;
    is_csr_mcause = 0;
    is_csr_mtval = 0;
    is_csr_mip = 0;
    is_csr_mcycle = 0;
    is_csr_mcycleh = 0;
    is_csr_minstret = 0;
    is_csr_minstreth = 0;
    is_csr_mvendorid = 0;
    is_csr_marchid = 0;
    is_csr_mimpid = 0;
    is_csr_mhartid = 0;
    is_csr_mconfigptr = 0;
    case (wb_rvfi.csr_addr)
      12'h300:
        is_csr_mstatus = 1;
      12'h301:
        is_csr_misa = 1;
      12'h304:
        is_csr_mie = 1;
      12'h305:
        is_csr_mtvec = 1;
      12'h340:
        is_csr_mscratch = 1;
      12'h341:
        is_csr_mepc = 1;
      12'h342:
        is_csr_mcause = 1;
      12'h343:
        is_csr_mtval = 1;
      12'h344:
        is_csr_mip = 1;
      12'hB00:
        is_csr_mcycle = 1;
      12'hb80:
        is_csr_mcycleh = 1;
      12'hB02:
        is_csr_minstret = 1;
      12'hb82:
        is_csr_minstreth = 1;
      12'hf11:
        is_csr_mvendorid = 1;
      12'hf12:
        is_csr_marchid = 1;
      12'hf13:
        is_csr_mimpid = 1;
      12'hf14:
        is_csr_mhartid = 1;
      12'hf15:
        is_csr_mconfigptr = 1;
      default:
        ;
    endcase
  end

  always_ff @(posedge clk_i)
  begin
    if (rst_i)
    begin
      rvfi_valid <= 0;
      rvfi_order <= 0;
      rvfi_insn <= 0;
      rvfi_trap <= 0;
      rvfi_halt <= 0;
      rvfi_intr <= 0;
      rvfi_mode <= 3;
      rvfi_ixl <= 1;

      rvfi_rs1_addr <= 0;
      rvfi_rs2_addr <= 0;
      rvfi_rs1_rdata <= 0;
      rvfi_rs2_rdata <= 0;

      rvfi_rd_addr <= 0;
      rvfi_rd_wdata <= 0;

      rvfi_pc_rdata <= 0;
      rvfi_pc_wdata <= 0;

      rvfi_mem_addr <= 0;
      rvfi_mem_rmask <= 0;
      rvfi_mem_wmask <= 0;
      rvfi_mem_rdata <= 0;
      rvfi_mem_wdata <= 0;

      rvfi_csr_mcycle_rmask <= 0;
      rvfi_csr_mcycle_wmask <= 0;
      rvfi_csr_mcycle_rdata <= 0;
      rvfi_csr_mcycle_wdata <= 0;

      rvfi_csr_minstret_rmask <= 0;
      rvfi_csr_minstret_wmask <= 0;
      rvfi_csr_minstret_rdata <= 0;
      rvfi_csr_minstret_wdata <= 0;

      rvfi_csr_mcause_rmask <= 0;
      rvfi_csr_mcause_wmask <= 0;
      rvfi_csr_mcause_rdata <= 0;
      rvfi_csr_mcause_wdata <= 0;

      rvfi_csr_mtvec_rmask <= 0;
      rvfi_csr_mtvec_wmask <= 0;
      rvfi_csr_mtvec_rdata <= 0;
      rvfi_csr_mtvec_wdata <= 0;

      rvfi_csr_mepc_rmask <= 0;
      rvfi_csr_mepc_wmask <= 0;
      rvfi_csr_mepc_rdata <= 0;
      rvfi_csr_mepc_wdata <= 0;
    end
    else
    begin
      rvfi_valid <= rvfi_valid_next;
      if (rvfi_valid_next)
        rvfi_order <= rvfi_order + 1;
      rvfi_mode <= 3;
      rvfi_ixl  <= 1;
      rvfi_halt <= 0;
      rvfi_trap <= wb_rvfi.trap_valid;
      rvfi_intr <= wb_rvfi.intr;

      if (wb_rvfi.trap_valid)
      begin
        rvfi_insn <= wb_rvfi.rvfi_trap_info.insn;
        rvfi_rs1_addr <= wb_rvfi.rvfi_trap_info.rs1_addr;
        rvfi_rs2_addr <= wb_rvfi.rvfi_trap_info.rs2_addr;
        rvfi_rs1_rdata <= wb_rvfi.rvfi_trap_info.rs1_rdata;
        rvfi_rs2_rdata <= wb_rvfi.rvfi_trap_info.rs2_rdata;

        rvfi_rd_addr <= wb_rvfi.rvfi_trap_info.rd_addr;
        rvfi_rd_wdata <= wb_rvfi.rvfi_trap_info.rd_wdata;

        rvfi_pc_rdata <= wb_rvfi.rvfi_trap_info.pc;
        rvfi_pc_wdata <= wb_rvfi.rvfi_trap_info.next_pc;

        rvfi_mem_addr <= wb_rvfi.mem_addr;
        rvfi_mem_rmask <= wb_rvfi.mem_rmask;
        rvfi_mem_wmask <= wb_rvfi.mem_wmask;
        rvfi_mem_rdata <= wb_rvfi.mem_rdata;
        rvfi_mem_wdata <= wb_rvfi.mem_wdata;
      end
      else
      begin
        rvfi_insn <= wb_rvfi.insn;
        rvfi_rs1_addr <= wb_rvfi.rs1_addr;
        rvfi_rs2_addr <= wb_rvfi.rs2_addr;
        rvfi_rs1_rdata <= wb_rvfi.rs1_rdata;
        rvfi_rs2_rdata <= wb_rvfi.rs2_rdata;

        rvfi_rd_addr <= wb_rvfi.rd_addr;
        rvfi_rd_wdata <= wb_rvfi.rd_wdata;

        rvfi_pc_rdata <= wb_rvfi.pc_rdata;
        rvfi_pc_wdata <= wb_rvfi.trap_valid ? trap_handler_addr_q : wb_rvfi.pc_wdata;

        rvfi_mem_addr <= wb_rvfi.mem_addr;
        rvfi_mem_rmask <= wb_rvfi.mem_rmask;
        // shift wmask and wdata if first nonzero bit is not at the lsb
        // riscv formal expects this format
        rvfi_mem_wmask <= wb_rvfi.mem_wmask >> get_shift(wb_rvfi.mem_wmask);
        rvfi_mem_rdata <= wb_rvfi.mem_rdata;
        rvfi_mem_wdata <= wb_rvfi.mem_wdata >> 8 * get_shift(wb_rvfi.mem_wmask);
      end


      // make rmask and wmask cleared if an exception
      rvfi_csr_mcycle_wmask <= is_csr_mcycleh ? {wb_csr_wmask, 32'd0} :
                            is_csr_mcycle  ? {32'd0, wb_csr_wmask} :
                            64'd0;
      rvfi_csr_minstret_wmask <= is_csr_minstreth ? {wb_csr_wmask, 32'd0} :
                              is_csr_minstret  ? {32'd0, wb_csr_wmask} :
                              64'd0;
      rvfi_csr_mcause_wmask <= is_csr_mcause ? wb_csr_wmask : 32'd0;
      rvfi_csr_mepc_wmask <= is_csr_mepc ? wb_csr_wmask : 32'd0;
      rvfi_csr_mtvec_wmask <= is_csr_mtvec ? wb_csr_wmask : 32'd0;
      // csr rmask logic
      rvfi_csr_mcycle_rmask <= is_csr_mcycleh ? {wb_csr_rmask, 32'd0} :
                            is_csr_mcycle  ? {32'd0, wb_csr_rmask} :
                            64'd0;
      rvfi_csr_minstret_rmask <= is_csr_minstreth ?  {wb_csr_rmask, 32'd0} :
                              is_csr_minstret  ? {32'd0, wb_csr_rmask} :
                              64'd0;
      rvfi_csr_mcause_rmask <= is_csr_mcause ? wb_csr_rmask : 32'd0;
      rvfi_csr_mtvec_rmask <= is_csr_mtvec ? wb_csr_rmask : 32'd0;
      rvfi_csr_mepc_rmask <= is_csr_mepc ? wb_csr_rmask : 32'd0;

      rvfi_csr_mcycle_rdata <= is_csr_mcycleh ? {wb_rvfi.csr_rdata, 32'd0} :
                            is_csr_mcycle  ? {32'd0, wb_rvfi.csr_rdata} :
                            64'd0;
      rvfi_csr_minstret_rdata <= is_csr_minstreth ? {wb_rvfi.csr_rdata, 32'd0} :
                              is_csr_minstret  ? {32'd0, wb_rvfi.csr_rdata} :
                              64'd0;
      // csr rdata logic
      rvfi_csr_mcause_rdata <= is_csr_mcause ? wb_rvfi.csr_rdata : 32'd0;
      rvfi_csr_mtvec_rdata <= is_csr_mtvec ? wb_rvfi.csr_rdata : 32'd0;
      rvfi_csr_mepc_rdata <= is_csr_mepc ? wb_rvfi.csr_rdata : 32'd0;

      rvfi_csr_mcycle_wdata <= is_csr_mcycleh ? {wb_rvfi.csr_wdata, 32'd0} :
                            is_csr_mcycle  ? {32'd0, wb_rvfi.csr_wdata} :
                            64'd0;
      rvfi_csr_minstret_wdata <= is_csr_minstreth ? {wb_rvfi.csr_wdata, 32'd0} :
                              is_csr_minstret  ? {32'd0, wb_rvfi.csr_wdata} :
                              64'd0;
      rvfi_csr_mcause_wdata <= is_csr_mcause ? wb_rvfi.csr_wdata : 32'd0;
      rvfi_csr_mtvec_wdata <= is_csr_mtvec ? wb_rvfi.csr_wdata : 32'd0;
      rvfi_csr_mepc_wdata <= is_csr_mepc ? wb_rvfi.csr_wdata : 32'd0;

    end
  end

  // Returns the shift amount (LSB index of the mask)
  function integer get_shift;
    input [3:0] wmask;
    integer i;
    logic   found;
    begin
      get_shift = 0;  // default
      found = 0;
      for (i = 0; i < 4; i = i + 1)
      begin
        if (!found && wmask[i])
        begin
          get_shift = i;
          found = 1;
        end
      end
    end
  endfunction

`endif

endmodule
