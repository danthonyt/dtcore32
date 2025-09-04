module ex_stage
  import params_pkg::*;
(
    // forward data
    input logic [2:0] ex_forward_a_sel_i,
    input logic [2:0] ex_forward_b_sel_i,
    input logic [31:0] mem_alu_csr_result_i,
    input logic [31:0] wb_load_rdata_i,
    input logic [31:0] wb_alu_csr_result_i,
    // goes to the if stage
    output logic ex_is_pc_redirect_o,
    output logic [31:0] ex_pc_target_o,
    input id_ex_t ex_pipeline_q,
    output ex_mem_t ex_pipeline_d
);

  trap_info_t ex_trap_d;
  logic [31:0] ex_rs1_rdata_d;
  logic [31:0] ex_rs2_rdata_d;
  logic [4:0] ex_rs1_addr_d;
  logic [4:0] ex_rs2_addr_d;
  logic [11:0] ex_csr_addr_d;
  logic [31:0] ex_csr_bitmask_comb;
  logic [31:0] ex_csr_wdata_d;
  logic [31:0] ex_next_pc_d;

  logic [31:0] ex_src_a_tick_comb;
  logic [31:0] ex_src_a_comb;
  logic [31:0] ex_src_b_comb;
  logic [31:0] ex_pc_base;
  logic ex_branch_cond_comb;
  logic ex_misaligned_jump_or_branch_comb;
  logic [4:0] ex_rd_addr_d;
  logic [31:0] ex_alu_result_comb;
  logic [31:0] ex_pc_target_non_jalr;
  logic [31:0] ex_alu_csr_result_d;
  logic [31:0] ex_store_wdata_d;


  // generate a trap on misaligned jumps or branches
  always_comb begin
    ex_trap_d = '{default: 0};
    if (ex_pipeline_q.carried_trap.valid) ex_trap_d = ex_pipeline_q.carried_trap;
    else if (ex_misaligned_jump_or_branch_comb)
      ex_trap_d = '{
          valid: 1,
          is_interrupt: 0,
          insn: ex_pipeline_q.insn,
          mcause: TRAP_CODE_INSTR_ADDR_MISALIGNED,
          pc: ex_pipeline_q.pc,
          next_pc: ex_next_pc_d,
          rs1_addr: ex_pipeline_q.rs1_addr,
          rs2_addr: ex_pipeline_q.rs2_addr,
          rd_addr: ex_pipeline_q.rd_addr,
          rs1_rdata: ex_rs1_rdata_d,
          rs2_rdata: ex_rs2_rdata_d,
          rd_wdata: 0
      };
    else ex_trap_d = '{default: 0};
  end


  assign ex_rs1_rdata_d = ex_src_a_tick_comb;
  assign ex_rs2_rdata_d = ex_store_wdata_d;
  assign ex_next_pc_d = (ex_is_pc_redirect_o) ? ex_pc_target_o : ex_pipeline_q.pc_plus_4;
  // trap if a jump or branch address is misaligned
  //assign ex_misaligned_jump_or_branch_comb = ex_is_pc_redirect_o & (ex_next_pc_d[1] | ex_next_pc_d[0]);
  assign ex_misaligned_jump_or_branch_comb = ex_is_pc_redirect_o & (ex_next_pc_d[1] | ex_next_pc_d[0]);

  assign ex_pc_target_non_jalr = (ex_pc_base + ex_pipeline_q.imm_ext);
  assign ex_pc_target_o     = (ex_pipeline_q.cf_op == CF_JALR) ? (ex_pc_target_non_jalr & ~(1'b1)) : ex_pc_target_non_jalr;
  assign ex_is_pc_redirect_o = (ex_pipeline_q.cf_op[0] | (ex_pipeline_q.cf_op[1] & ex_branch_cond_comb));

  // disable ex stage if trap propagates from previous stage
  // disable jumps, and set all register addresses to zero
  assign ex_rs1_addr_d = ex_pipeline_q.rs1_addr;
  assign ex_rs2_addr_d = ex_pipeline_q.rs2_addr;
  assign ex_rd_addr_d = ex_pipeline_q.rd_addr;
  assign ex_csr_addr_d = ex_pipeline_q.csr_addr;

  // alu input 1 data path
  // select reg 1 data or data forwarded from WB or MEM stage
  always_comb begin
    case (ex_forward_a_sel_i)
      NO_FORWARD_SEL:             ex_src_a_tick_comb = ex_pipeline_q.rs1_rdata;
      FORWARD_SEL_MEM_ALU_RESULT: ex_src_a_tick_comb = mem_alu_csr_result_i;
      FORWARD_SEL_WB_LOAD_RDATA:  ex_src_a_tick_comb = wb_load_rdata_i;
      FORWARD_SEL_WB_ALU_RESULT:  ex_src_a_tick_comb = wb_alu_csr_result_i;
      default:                    ex_src_a_tick_comb = 0;
    endcase
  end
  // select data from first mux, zero, or pc
  always_comb begin
    case (ex_pipeline_q.alu_a_sel)
      ALU_A_SEL_REG_DATA: ex_src_a_comb = ex_src_a_tick_comb;
      ALU_A_SEL_ZERO:     ex_src_a_comb = 0;
      ALU_A_SEL_PC:       ex_src_a_comb = ex_pipeline_q.pc;
      default:            ex_src_a_comb = 0;
    endcase
  end
  // alu input 2 data path
  // select reg 2 data or data forwarded from WB or MEM stage
  always_comb begin
    case (ex_forward_b_sel_i)
      NO_FORWARD_SEL:             ex_store_wdata_d = ex_pipeline_q.rs2_rdata;
      FORWARD_SEL_MEM_ALU_RESULT: ex_store_wdata_d = mem_alu_csr_result_i;
      FORWARD_SEL_WB_LOAD_RDATA:  ex_store_wdata_d = wb_load_rdata_i;
      FORWARD_SEL_WB_ALU_RESULT:  ex_store_wdata_d = wb_alu_csr_result_i;
      default:                    ex_store_wdata_d = 0;
    endcase
  end
  // select data from first mux, or extended immediate
  always_comb begin
    unique case (ex_pipeline_q.alu_b_sel)
      ALU_B_SEL_REG_DATA: ex_src_b_comb = ex_store_wdata_d;
      ALU_B_SEL_IMM:      ex_src_b_comb = ex_pipeline_q.imm_ext;
    endcase
  end
  // select base address for branch/jump address, selecting either
  // the current pc or reg1_data.
  always_comb begin
    unique case (ex_pipeline_q.pc_alu_sel)
      PC_ALU_SEL_PC:       ex_pc_base = ex_pipeline_q.pc;
      PC_ALU_SEL_REG_DATA: ex_pc_base = ex_src_a_tick_comb;
    endcase
  end
  // select write value to be used in a csr instruction
  always_comb begin
    unique case (ex_pipeline_q.csr_bitmask_sel)
      CSR_BITMASK_SEL_REG_DATA: ex_csr_bitmask_comb = ex_src_a_tick_comb;
      CSR_BITMASK_SEL_IMM:      ex_csr_bitmask_comb = ex_pipeline_q.imm_ext;
    endcase
  end

  always_comb begin
    ex_csr_wdata_d = 0;
    case (ex_pipeline_q.csr_op)
      CSR_WRITE: ex_csr_wdata_d = ex_csr_bitmask_comb;
      CSR_CLEAR: ex_csr_wdata_d = (ex_pipeline_q.csr_rdata & ~ex_csr_bitmask_comb);
      CSR_SET:   ex_csr_wdata_d = (ex_pipeline_q.csr_rdata | ex_csr_bitmask_comb);
      default:   ;
    endcase
  end


  assign ex_alu_csr_result_d = (ex_pipeline_q.csr_op != CSR_NONE) ? ex_pipeline_q.csr_rdata : ex_alu_result_comb;

  alu alu_inst (
      .a_i(ex_src_a_comb),
      .b_i(ex_src_b_comb),
      .control_i(ex_pipeline_q.alu_control),
      .branch_cond_o(ex_branch_cond_comb),
      .result_o(ex_alu_result_comb)
  );

  always_comb begin
    ex_pipeline_d.pc              = ex_pipeline_q.pc;
    ex_pipeline_d.pc_plus_4       = ex_pipeline_q.pc_plus_4;
    ex_pipeline_d.next_pc         = ex_next_pc_d;
    ex_pipeline_d.insn            = ex_pipeline_q.insn;
    ex_pipeline_d.valid           = ex_pipeline_q.valid;
    ex_pipeline_d.intr            = ex_pipeline_q.intr;
    ex_pipeline_d.rs1_addr        = ex_rs1_addr_d;
    ex_pipeline_d.rs2_addr        = ex_rs2_addr_d;
    ex_pipeline_d.rd_addr         = ex_rd_addr_d;
    ex_pipeline_d.rs1_rdata       = ex_src_a_tick_comb;
    ex_pipeline_d.rs2_rdata       = ex_store_wdata_d;
    ex_pipeline_d.csr_addr        = ex_csr_addr_d;
    ex_pipeline_d.csr_wdata       = ex_csr_wdata_d;
    ex_pipeline_d.csr_rdata       = ex_pipeline_q.csr_rdata;
    ex_pipeline_d.result_sel      = ex_pipeline_q.result_sel;
    ex_pipeline_d.mem_op          = ex_pipeline_q.mem_op;
    ex_pipeline_d.store_wdata     = ex_store_wdata_d;
    ex_pipeline_d.alu_csr_result  = ex_alu_csr_result_d;
    ex_pipeline_d.carried_trap    = ex_trap_d;
  end

endmodule
