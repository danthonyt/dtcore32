module ex_stage
  import params_pkg::*;
(
    input logic ex_mem_stall_i,
    input logic ex_mem_flush_i,
    // forward data
    input logic [2:0] ex_forward_a_sel_i,
    input logic [2:0] ex_forward_b_sel_i,
    input logic [31:0] mem_alu_csr_result_i,
    input logic [31:0] wb_result_i,
    // goes to the if stage
    output logic ex_is_pc_redirect_o,
    output logic [31:0] ex_pc_target_o,
    input id_ex_t ex_pipeline_q,
    output ex_mem_t ex_pipeline_d,
    output logic [4:0] ex_rs1_addr_o,
    output logic [4:0] ex_rs2_addr_o,
    // trap info
    output logic ex_trap_valid_o
);

//*****************************************************************
//
//
// SIGNAL DECLARATIONS
//
//
//*****************************************************************
  logic [4:0] ex_rs1_addr_gated;
  logic [4:0] ex_rs2_addr_gated;
  cf_op_t ex_cf_op_gated;
  logic ex_trap_valid_gated;


  logic [4:0] ex_rs1_addr_d;
  logic [4:0] ex_rs2_addr_d;
  logic [11:0] ex_csr_addr_d;
  logic [31:0] ex_csr_bitmask;
  logic [31:0] ex_csr_wdata_d;


  logic [31:0] ex_src_a_tick_comb;
  logic [31:0] ex_src_a;
  logic [31:0] ex_src_b;
  logic [31:0] ex_pc_base;
  logic ex_branch_cond;
  logic ex_misaligned_jump_or_branch_comb;
  logic [4:0] ex_rd_addr_d;
  logic [31:0] ex_alu_result;
  logic [31:0] ex_alu_csr_result;
  logic [31:0] ex_pc_target_non_jalr;
  logic [31:0] ex_store_wdata_d;
  logic ex_trap_valid_raw;


//*****************************************************************
//
//
// ASSIGNMENTS
//
//
//*****************************************************************
  // trap if a jump or branch address is misaligned
  //assign ex_misaligned_jump_or_branch_comb = ex_is_pc_redirect_o & (ex_next_pc_d[1] | ex_next_pc_d[0]);
  // generate misaligned trap in parallel to avoid additional combinational delay
  assign ex_misaligned_jump_or_branch_comb = ex_is_pc_redirect_o & (ex_pc_target_o[1] | ex_pc_target_o[0]);

  assign ex_pc_target_non_jalr = (ex_pc_base + ex_pipeline_q.imm_ext);
  assign ex_pc_target_o     = (ex_cf_op_gated == CF_JALR) ? (ex_pc_target_non_jalr & ~(1'b1)) : ex_pc_target_non_jalr;
  assign ex_is_pc_redirect_o = (ex_cf_op_gated[0] | (ex_cf_op_gated[1] & ex_branch_cond));

  // disable ex stage if trap propagates from previous stage
  // disable jumps, and set all register addresses to zero
  assign ex_rs1_addr_d = ex_rs1_addr_gated;
  assign ex_rs2_addr_d = ex_rs2_addr_gated;
  assign ex_rd_addr_d = ex_pipeline_q.rd_addr;
  assign ex_csr_addr_d = ex_pipeline_q.csr_addr;

  assign ex_rs1_addr_o = ex_rs1_addr_d;
  assign ex_rs2_addr_o = ex_rs2_addr_d;

  assign ex_alu_csr_result = (ex_pipeline_q.csr_op != MEM_NONE) ? ex_alu_result : ex_pipeline_q.csr_rdata;

  // alu input 1 data path
  // select reg 1 data or data forwarded from WB or MEM stage
  always_comb begin
    ex_src_a = 0;
    if (ex_pipeline_q.alu_a_sel == ALU_A_SEL_REG_DATA) begin  // sele
      if (ex_forward_a_sel_i == FORWARD_SEL_WB_RESULT) ex_src_a = wb_result_i;
      else if (ex_forward_a_sel_i == FORWARD_SEL_MEM_RESULT) ex_src_a = mem_alu_csr_result_i;
      else ex_src_a = ex_pipeline_q.rs1_rdata;
    end else if (ex_pipeline_q.alu_a_sel == ALU_A_SEL_PC) ex_src_a = ex_pipeline_q.pc;
  end
  // alu input 2 data path
  // select reg 2 data or data forwarded from WB or MEM stage
  always_comb begin
    ex_src_b = 0;
    if (ex_pipeline_q.alu_b_sel == ALU_B_SEL_REG_DATA) begin  // sele
      if (ex_forward_b_sel_i == FORWARD_SEL_WB_RESULT) ex_src_b = wb_result_i;
      else if (ex_forward_b_sel_i == FORWARD_SEL_MEM_RESULT) ex_src_b = mem_alu_csr_result_i;
      else ex_src_b = ex_pipeline_q.rs2_rdata;
    end else if (ex_pipeline_q.alu_a_sel == ALU_B_SEL_IMM) ex_src_b = ex_pipeline_q.imm_ext;
  end
  // select base address for branch/jump address, selecting either
  // the current pc or reg1_data.
  always_comb begin
    unique case (ex_pipeline_q.pc_alu_sel)
      PC_ALU_SEL_PC:       ex_pc_base = ex_pipeline_q.pc;
      PC_ALU_SEL_REG_DATA: ex_pc_base = ex_src_a;
    endcase
  end
  // select write value to be used in a csr instruction
  always_comb begin
    unique case (ex_pipeline_q.csr_bitmask_sel)
      CSR_BITMASK_SEL_REG_DATA: ex_csr_bitmask = ex_src_a;
      CSR_BITMASK_SEL_IMM:      ex_csr_bitmask = ex_pipeline_q.imm_ext;
    endcase
  end

  always_comb begin
    ex_csr_wdata_d = 0;
    case (ex_pipeline_q.csr_op)
      CSR_WRITE: ex_csr_wdata_d = ex_csr_bitmask;
      CSR_CLEAR: ex_csr_wdata_d = (ex_pipeline_q.csr_rdata & ~ex_csr_bitmask);
      CSR_SET:   ex_csr_wdata_d = (ex_pipeline_q.csr_rdata | ex_csr_bitmask);
      default:   ;
    endcase
  end

  

  always_comb begin
    ex_rs1_addr_gated = ex_pipeline_q.rs1_addr;
    ex_rs2_addr_gated = ex_pipeline_q.rs2_addr;
    ex_cf_op_gated = ex_pipeline_q.cf_op;
    ex_trap_valid_gated = ex_trap_valid_raw;
    if (!ex_pipeline_q.valid || ex_pipeline_q.stall || ex_pipeline_q.flush) begin
      ex_rs1_addr_gated = 0;
      ex_rs2_addr_gated = 0;
      ex_cf_op_gated = cf_op_t'(0);
      ex_trap_valid_gated = 0;
    end
  end
  always_comb begin
    ex_pipeline_d.stall          = ex_mem_stall_i;
    ex_pipeline_d.flush          = ex_mem_flush_i;
    ex_pipeline_d.pc             = ex_pipeline_q.pc;
    ex_pipeline_d.pc_plus_4      = ex_pipeline_q.pc_plus_4;
    ex_pipeline_d.valid          = ex_pipeline_q.valid;
    ex_pipeline_d.rd_addr        = ex_rd_addr_d;
    ex_pipeline_d.csr_addr       = ex_csr_addr_d;
    ex_pipeline_d.csr_wdata      = ex_csr_wdata_d;
    ex_pipeline_d.mem_op         = ex_pipeline_q.mem_op;
    ex_pipeline_d.store_wdata    = ex_store_wdata_d;
    ex_pipeline_d.alu_csr_result = ex_alu_csr_result;
  end
  always_comb begin
    ex_trap_valid_raw = 0;
    ex_pipeline_d.trap_mcause = 'x;
    ex_pipeline_d.trap_pc = 'x;

    if (ex_pipeline_q.trap_valid) begin
      ex_trap_valid_raw = 1;
      ex_pipeline_d.trap_mcause = ex_pipeline_q.trap_mcause;
      ex_pipeline_d.trap_pc = ex_pipeline_q.trap_pc;
    end else if (ex_misaligned_jump_or_branch_comb) begin
      ex_trap_valid_raw = 1;
      ex_pipeline_d.trap_mcause = {1'b0, TRAP_CODE_INSTR_ADDR_MISALIGNED};
      ex_pipeline_d.trap_pc = ex_pipeline_q.pc;
    end
  end
  assign ex_pipeline_d.trap_valid = ex_trap_valid_gated;
  // only carried traps trigger a flush
  assign ex_trap_valid_o = ex_pipeline_q.trap_valid;
  // traps generated in ex stage carry to the mem
  // stage 

//*****************************************************************
//
//
// INSTANTIATIONS
//
//
//*****************************************************************
alu alu_inst (
      .a_i(ex_src_a),
      .b_i(ex_src_b),
      .control_i(ex_pipeline_q.alu_control),
      .branch_cond_o(ex_branch_cond),
      .result_o(ex_alu_result)
  );
//*****************************************************************
//
//
// RISCV_FORMAL
//
//
//*****************************************************************

`ifdef RISCV_FORMAL
  trap_info_t ex_trap_d;
  logic [31:0] ex_next_pc_d;
  assign ex_next_pc_d = (ex_is_pc_redirect_o) ? ex_pc_target_o : ex_pipeline_q.pc_plus_4;
  always_comb begin
    ex_trap_d.insn = ex_pipeline_q.insn;
    ex_trap_d.pc = ex_pipeline_q.pc;
    ex_trap_d.next_pc = ex_next_pc_d;
    ex_pipeline_d.csr_rdata = ex_pipeline_q.csr_rdata;
    ex_trap_d.rs1_addr = ex_rs1_addr_gated;
    ex_trap_d.rs2_addr = ex_rs2_addr_gated;
    ex_trap_d.rd_addr = ex_pipeline_q.rd_addr;
    ex_trap_d.rs1_rdata = ex_src_a_tick_comb;
    ex_trap_d.rs2_rdata = ex_store_wdata_d;
    ex_trap_d.rd_wdata = 0;
    if (ex_pipeline_q.trap_valid) begin
      ex_trap_d = ex_pipeline_q.rvfi_trap_info;
    end
  end

  always_comb begin
    ex_pipeline_d.next_pc        = ex_next_pc_d;
    ex_pipeline_d.insn           = ex_pipeline_q.insn;
    ex_pipeline_d.intr           = ex_pipeline_q.intr;
    ex_pipeline_d.rs1_addr       = ex_rs1_addr_o;
    ex_pipeline_d.rs2_addr       = ex_rs2_addr_o;
    ex_pipeline_d.rs1_rdata      = ex_src_a_tick_comb;
    ex_pipeline_d.rs2_rdata      = ex_store_wdata_d;
    ex_pipeline_d.rvfi_trap_info = ex_trap_d;
  end
`endif
endmodule
