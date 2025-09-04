module wb_stage
  import params_pkg::*;
(
    input mem_wb_t wb_pipeline_q,
    // from csr file
    input logic [31:0] wb_csr_rmask_i,
    input logic [31:0] wb_csr_wmask_i,
    // to csr file 
    output logic [11:0] wb_csr_addr_o,
    output logic [31:0] wb_csr_wdata_o,
    // to regfile
    output logic [4:0] wb_rd_addr_o,
    output logic [31:0] wb_rd_wdata_o,
    // for trap handling
    output logic wb_trap_valid_o,
    // for riscv formal monitoring
    output rvfi_t rvfi_o

);
  trap_info_t wb_trap_d;
  logic [4:0] wb_rd_addr_masked;
  logic [31:0] wb_rd_wdata_masked;
  logic [31:0] wb_rd_wdata_comb;
  logic [11:0] wb_csr_addr_masked;

  assign wb_trap_valid_o = wb_trap_d.valid;
  assign wb_trap_d = wb_pipeline_q.carried_trap.valid ? wb_pipeline_q.carried_trap : '{default: 0};

  // trap disable logic
  assign wb_rd_addr_masked = wb_pipeline_q.carried_trap.valid ? 0 : wb_pipeline_q.rd_addr;
  assign wb_csr_addr_masked = wb_pipeline_q.carried_trap.valid ? 0 : wb_pipeline_q.csr_addr;

  // disable register and csr writes for an excepted instruction
  // make sure that instructions that dont write to any register address have x0 as rd and 0 as rd_wdata
  assign wb_rd_wdata_masked = (wb_rd_addr_masked != 0) ? wb_rd_wdata_comb : 0;
  always_comb begin
    unique case (wb_pipeline_q.result_sel)
      RESULT_SEL_ALU_RESULT: wb_rd_wdata_comb = wb_pipeline_q.alu_csr_result;
      RESULT_SEL_MEM_DATA: wb_rd_wdata_comb = wb_pipeline_q.load_rdata;
      RESULT_SEL_NEXT_INSTR_ADDR: wb_rd_wdata_comb = wb_pipeline_q.pc_plus_4;
      RESULT_SEL_CSR_READ_DATA: wb_rd_wdata_comb = wb_pipeline_q.csr_rdata;
    endcase
  end

  assign wb_csr_addr_o = wb_csr_addr_masked;
  assign wb_rd_addr_o  = wb_rd_addr_masked;
  assign wb_rd_wdata_o = wb_rd_wdata_masked;
  assign wb_csr_wdata_o = wb_pipeline_q.csr_wdata;

  always_comb begin
    // PC + instruction flow
    rvfi_o.pc_rdata  = wb_pipeline_q.pc;
    rvfi_o.pc_wdata  = wb_pipeline_q.next_pc;
    rvfi_o.insn      = wb_pipeline_q.insn;
    rvfi_o.valid     = wb_pipeline_q.valid;
    rvfi_o.intr      = wb_pipeline_q.intr;

    // Register file signals
    rvfi_o.rs1_addr  = wb_pipeline_q.rs1_addr;
    rvfi_o.rs2_addr  = wb_pipeline_q.rs2_addr;
    rvfi_o.rd_addr   = wb_rd_addr_masked;
    rvfi_o.rs1_rdata = wb_pipeline_q.rs1_rdata;
    rvfi_o.rs2_rdata = wb_pipeline_q.rs2_rdata;
    rvfi_o.rd_wdata  = wb_rd_wdata_masked;

    // CSR signals
    rvfi_o.csr_addr  = wb_csr_addr_masked;
    rvfi_o.csr_wdata = wb_pipeline_q.csr_wdata;
    rvfi_o.csr_wmask = wb_csr_wmask_i;
    rvfi_o.csr_rdata = wb_pipeline_q.csr_rdata;
    rvfi_o.csr_rmask = wb_csr_rmask_i;

    // Memory interface
    rvfi_o.mem_addr = wb_pipeline_q.alu_csr_result;
    rvfi_o.mem_rmask = wb_pipeline_q.load_rmask;
    rvfi_o.mem_rdata = wb_pipeline_q.load_rdata;
    rvfi_o.mem_wmask = wb_pipeline_q.store_wmask;
    rvfi_o.mem_wdata = wb_pipeline_q.store_wdata;

    // Trap info
    rvfi_o.trap      = wb_trap_d;
  end

endmodule
