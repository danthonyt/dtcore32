module wb_stage
  import params_pkg::*;
(
    input mem_wb_t wb_pipeline_q,
    // to csr file 
    output logic [11:0] wb_csr_addr_o,
    output logic [31:0] wb_csr_wdata_o,
    // to regfile
    output logic [4:0] wb_rd_addr_o,
    output logic [31:0] wb_rd_wdata_o,
    // trap data to csrfile
    output logic wb_trap_valid_o,
    output logic [31:0] wb_trap_mcause_o,
    output logic [31:0] wb_trap_pc_o
);

  logic [ 4:0] rd_addr_gated;
  logic [11:0] csr_addr_gated;
  logic [31:0] rd_wdata_gated;
  logic        trap_valid_gated;
  logic [ 4:0] wb_rd_addr;
  logic [31:0] wb_rd_wdata;
  logic [11:0] wb_csr_addr;

  // gated signals on valid, previous stall, or flush 
  always_comb begin
    rd_addr_gated = wb_pipeline_q.rd_addr;
    csr_addr_gated = wb_pipeline_q.csr_addr;
    rd_wdata_gated = wb_pipeline_q.rd_wdata;
    trap_valid_gated = wb_pipeline_q.trap_valid;
    if (!wb_pipeline_q.valid || wb_pipeline_q.stall || wb_pipeline_q.flush) begin
      rd_addr_gated = '0;
      csr_addr_gated = '0;
      rd_wdata_gated = '0;
      trap_valid_gated = '0;
    end
  end

  // trap disable logic
  assign wb_rd_addr = trap_valid_gated ? 0 : rd_addr_gated;
  assign wb_csr_addr = trap_valid_gated ? 0 : csr_addr_gated;

  // disable register and csr writes for an excepted instruction
  // make sure that instructions that dont write to any register address have x0 as rd and 0 as rd_wdata
  assign wb_rd_wdata = (wb_rd_addr != 0) ? wb_pipeline_q.rd_wdata : 0;

  assign wb_csr_addr_o = wb_csr_addr;
  assign wb_rd_addr_o = wb_rd_addr;
  assign wb_rd_wdata_o = wb_rd_wdata;
  assign wb_csr_wdata_o = wb_pipeline_q.csr_wdata;

  assign wb_trap_valid_o = trap_valid_gated;
  assign wb_trap_mcause_o = wb_pipeline_q.trap_mcause;
  assign wb_trap_pc_o = wb_pipeline_q.trap_pc;

endmodule
