module id_stage
  import params_pkg::*;
(
    // from hazard control 
    input logic id_forward_a_i,
    input logic id_forward_b_i,
    // from regfile - combinational read
    input logic [31:0] regfile_rs1_rdata_i,
    input logic [31:0] regfile_rs2_rdata_i,
    // from csrfile - combinational read
    input logic [31:0] id_csrfile_rdata_i,
    output logic [11:0] id_csrfile_addr_o,
    // from writeback stage
    input logic [31:0] wb_rd_wdata_i,
    // pipeline
    input if_id_t id_pipeline_q,
    output id_ex_t id_pipeline_d
);

  logic [31:0] id_rs1_rdata_d;
  logic [31:0] id_rs2_rdata_d;
  logic [11:0] id_csr_addr_d;
  logic [31:0] id_imm_ext_d;
  logic [4:0] id_rd_addr_d;
  alu_control_t id_alu_control_d;
  logic [6:0] id_op_comb;
  logic [2:0] id_funct3_comb;
  logic id_funct7b5_comb;
  logic [6:0] id_funct7_comb;
  logic [11:0] id_funct12_comb;
  logic id_rtype_alt_comb;
  logic id_itype_alt_comb;
  logic id_rs1_valid_comb;
  logic id_rs2_valid_comb;
  logic id_rd_valid_comb;
  logic [30:0] id_maindec_mcause_comb;
  logic id_maindec_trap_valid_comb;
  mem_op_t id_mem_op_d;
  cf_op_t id_cf_op_d;
  csr_op_t id_csr_op_d;
  imm_ext_op_t id_imm_ext_op;
  alu_a_sel_t id_alu_a_sel_d;
  alu_b_sel_t id_alu_b_sel_d;
  pc_alu_sel_t id_pc_alu_sel_d;
  result_sel_t id_result_sel_d;
  csr_bitmask_sel_t id_csr_bitmask_sel_d;
  logic [4:0] id_rs1_addr_d;
  logic [4:0] id_rs2_addr_d;



  assign id_op_comb = id_pipeline_q.insn[6:0];
  assign id_funct3_comb = id_pipeline_q.insn[14:12];
  assign id_funct7b5_comb = id_pipeline_q.insn[30];
  assign id_funct7_comb = id_pipeline_q.insn[31:25];
  assign id_funct12_comb = id_pipeline_q.insn[31:20];

  assign id_rtype_alt_comb = id_op_comb[5] & id_funct7b5_comb;
  assign id_itype_alt_comb = ~id_op_comb[5] & id_funct7b5_comb;
  assign id_rs1_addr_d = (id_rs1_valid_comb) ? id_pipeline_q.insn[19:15] : 0;
  assign id_rs2_addr_d = (id_rs2_valid_comb) ? id_pipeline_q.insn[24:20] : 0;
  assign id_rd_addr_d = (id_rd_valid_comb) ? id_pipeline_q.insn[11:7] : 0;
  assign id_csr_addr_d = (id_csr_op_d != CSR_NONE) ? id_pipeline_q.insn[31:20] : 0;
  assign id_csrfile_addr_o = id_csr_addr_d;

  // select forwarded rs1 or rs2 rdata if needed
  assign id_rs1_rdata_d = id_forward_a_i ? wb_rd_wdata_i : regfile_rs1_rdata_i;
  assign id_rs2_rdata_d = id_forward_b_i ? wb_rd_wdata_i : regfile_rs2_rdata_i;

  decoder decoder_inst (
      .OP(id_op_comb),
      .FUNCT3(id_funct3_comb),
      .FUNCT7(id_funct7_comb),
      .FUNCT12(id_funct12_comb),
      .RS1_ADDR(id_rs1_addr_d),
      .RD_ADDR(id_rd_addr_d),
      .RTYPE_ALT(id_rtype_alt_comb),
      .ITYPE_ALT(id_itype_alt_comb),
      .RD_VALID(id_rd_valid_comb),
      .RS1_VALID(id_rs1_valid_comb),
      .RS2_VALID(id_rs2_valid_comb),
      .MEM_OP(id_mem_op_d),
      .CF_OP(id_cf_op_d),
      .CSR_OP(id_csr_op_d),
      .ALU_CONTROL(id_alu_control_d),
      .IMM_EXT_OP(id_imm_ext_op),
      .ALU_A_SRC(id_alu_a_sel_d),
      .ALU_B_SRC(id_alu_b_sel_d),
      .PC_ALU_SRC(id_pc_alu_sel_d),
      .RESULT_SRC(id_result_sel_d),
      .CSR_BITMASK_SEL(id_csr_bitmask_sel_d),
      .TRAP_MCAUSE(id_maindec_mcause_comb),
      .TRAP_VALID(id_maindec_trap_valid_comb)

  );

  extend extend_inst (
      .insn_i(id_pipeline_q.insn),
      .imm_ext_op_i(id_imm_ext_op),
      .imm_ext_o(id_imm_ext_d)
  );

  always_comb begin
    id_pipeline_d.pc              = id_pipeline_q.pc;
    id_pipeline_d.pc_plus_4       = id_pipeline_q.pc_plus_4;
    id_pipeline_d.valid           = id_pipeline_q.valid;
    id_pipeline_d.rs1_addr        = id_rs1_addr_d;
    id_pipeline_d.rs2_addr        = id_rs2_addr_d;
    id_pipeline_d.rd_addr         = id_rd_addr_d;
    id_pipeline_d.rs1_rdata       = id_rs1_rdata_d;
    id_pipeline_d.rs2_rdata       = id_rs2_rdata_d;
    id_pipeline_d.imm_ext         = id_imm_ext_d;
    id_pipeline_d.csr_addr        = id_csr_addr_d;
    id_pipeline_d.csr_rdata       = id_csrfile_rdata_i;
    id_pipeline_d.csr_op          = id_csr_op_d;
    id_pipeline_d.cf_op           = id_cf_op_d;
    id_pipeline_d.alu_control     = id_alu_control_d;
    id_pipeline_d.result_sel      = id_result_sel_d;
    id_pipeline_d.alu_a_sel       = id_alu_a_sel_d;
    id_pipeline_d.alu_b_sel       = id_alu_b_sel_d;
    id_pipeline_d.pc_alu_sel      = id_pc_alu_sel_d;
    id_pipeline_d.csr_bitmask_sel = id_csr_bitmask_sel_d;
    id_pipeline_d.mem_op          = id_mem_op_d;
  end

always_comb begin
    id_pipeline_d.trap_valid  = 0;
    id_pipeline_d.trap_mcause = 'x;
    id_pipeline_d.trap_pc = 'x;
    if (id_maindec_trap_valid_comb) begin
      id_pipeline_d.trap_valid  = 1;
      id_pipeline_d.trap_mcause = {1'd0, id_maindec_mcause_comb};
      id_pipeline_d.trap_pc = id_pipeline_q.pc;
    end
  end


`ifdef RISCV_FORMAL
  trap_info_t id_trap_d;
  always_comb begin
    id_trap_d.insn = id_pipeline_q.insn;
    id_trap_d.pc = id_pipeline_q.pc;
    id_trap_d.next_pc = 0;
    id_trap_d.rs1_addr = 0;
    id_trap_d.rs2_addr = 0;
    id_trap_d.rd_addr = 0;
    id_trap_d.rs1_rdata = 0;
    id_trap_d.rs2_rdata = 0;
    id_trap_d.rd_wdata = 0;
  end
  always_comb begin
    id_pipeline_d.insn = id_pipeline_q.insn;
    id_pipeline_d.intr = id_pipeline_q.intr;
    id_pipeline_d.rvfi_trap_info = id_trap_d;
  end
`endif
endmodule
