module id_stage
  import params_pkg::*;
(
    input logic clk_i,
    input logic rst_i,
    // to regfile - combinational read
    output logic [4:0] regfile_rs1_addr_o,
    output logic [4:0] regfile_rs2_addr_o,
    // from regfile - combinational read
    input logic [31:0] regfile_rs1_rdata_i,
    input logic [31:0] regfile_rs2_rdata_i,
    // to csrfile
    input if_id_t id_pipeline_q,
    output id_ex_t id_pipeline_d
);

  trap_info_t id_trap_d;
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
  logic id_forward_a_comb;
  logic id_forward_b_comb;
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

  csrfile csrfile_inst (
      .clk_i(clk_i),
      .rst_i(rst_i),
      .wb_rd_addr_i(wb_rd_addr_i),
      .csr_raddr_i(csr_raddr_i),
      .csr_waddr_i(csr_waddr_i),
      .csr_wdata_i(csr_wdata_i),
      .wb_valid_i(wb_valid_i),
      .wb_trap_i(wb_trap_i),
      .ex_valid_i(ex_valid_i),
      .mem_valid_i(mem_valid_i),
      .wb_valid_i(wb_valid_i),
      .trap_handler_addr_i(trap_handler_addr_i),
      .csr_rdata_q(csr_rdata_q),
      .csr_rmask_o(csr_rmask_o),
      .csr_wmask_o(csr_wmask_o)
  );

  // trap on an unknown instruction
  always_comb begin
    if (id_maindec_trap_valid_comb)
      id_trap_d = '{
          valid: 1,
          is_interrupt: 0,
          insn: id_pipeline.insn,
          mcause: id_maindec_mcause_comb,
          pc: id_pipeline.pc,
          next_pc: trap_handler_addr_q,
          rs1_addr: 0,
          rs2_addr: 0,
          rd_addr: 0,
          rs1_rdata: 0,
          rs2_rdata: 0,
          rd_wdata: 0
      };
    else id_trap_d = '{default: 0};
  end

  assign id_op_comb = id_pipeline_q.insn[6:0];
  assign id_funct3_comb = id_pipeline_q.insn[14:12];
  assign id_funct7b5_comb = id_pipeline_q.insn[30];
  assign id_funct7_comb = id_pipeline_q.insn[31:25];
  assign id_funct12_comb = id_pipeline_q.insn[31:20];

  assign id_rtype_alt_comb = id_op_comb[5] & id_funct7b5_comb;
  assign id_itype_alt_comb = ~id_op_comb[5] & id_funct7b5_comb;
  assign regfile_rs1_addr_o = (id_rs1_valid_comb) ? id_pipeline_q.insn[19:15] : 0;
  assign regfile_rs2_addr_o = (id_rs2_valid_comb) ? id_pipeline_q.insn[24:20] : 0;
  assign id_rd_addr_d = (id_rd_valid_comb) ? id_pipeline_q.insn[11:7] : 0;
  assign id_csr_addr_d = (id_csr_op_d != CSR_NONE) ? id_pipeline_q.insn[31:20] : 0;

  // select forwarded rs1 or rs2 rdata if needed
  assign id_rs1_rdata_d = id_forward_a_comb ? wb_rd_wdata_masked : regfile_rs1_rdata_i;
  assign id_rs2_rdata_d = id_forward_b_comb ? wb_rd_wdata_masked : regfile_rs2_rdata_i;

  decoder decoder_inst (
      .OP(id_op_comb),
      .FUNCT3(id_funct3_comb),
      .FUNCT7(id_funct7_comb),
      .FUNCT12(id_funct12_comb),
      .RS1_ADDR(regfile_rs1_addr_o),
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
      .IMM_EXT_OP(id_imm_ext_op),
      .IMM_EXT(id_imm_ext_d)
  );

  always_comb begin
    id_pipeline_d.pc              = id_pipeline_q.pc;
    id_pipeline_d.pc_plus_4       = id_pipeline_q.pc_plus_4;
    id_pipeline_d.insn            = id_pipeline_q.insn;
    id_pipeline_d.valid           = id_pipeline_q.valid;
    id_pipeline_d.intr            = id_pipeline_q.intr;
    id_pipeline_d.rs1_addr        = regfile_rs1_addr_o;
    id_pipeline_d.rs2_addr        = regfile_rs2_addr_o;
    id_pipeline_d.rd_addr         = id_rd_addr_d;
    id_pipeline_d.rs1_rdata       = id_rs1_rdata_d;
    id_pipeline_d.rs2_rdata       = id_rs2_rdata_d;
    id_pipeline_d.imm_ext         = id_imm_ext_d;
    id_pipeline_d.csr_addr        = id_csr_addr_d;
    id_pipeline_d.csr_op          = id_csr_op_d;
    id_pipeline_d.cf_op           = id_cf_op_d;
    id_pipeline_d.alu_control     = id_alu_control_d;
    id_pipeline_d.result_sel      = id_result_sel_d;
    id_pipeline_d.alu_a_sel       = id_alu_a_sel_d;
    id_pipeline_d.alu_b_sel       = id_alu_b_sel_d;
    id_pipeline_d.pc_alu_sel      = id_pc_alu_sel_d;
    id_pipeline_d.csr_bitmask_sel = id_csr_bitmask_sel_d;
    id_pipeline_d.mem_op          = id_mem_op_d;
    id_pipeline_d.carried_trap    = id_trap_d;
  end

  /******************************************/
  //
  //    FORMAL VERIFICATION
  //
  /******************************************/
`ifdef FORMAL
  default clocking @(posedge clk_i);
  endclocking
  initial assume (rst_i);

`endif
endmodule
