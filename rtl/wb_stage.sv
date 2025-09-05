module wb_stage
  import params_pkg::*;
(
    input mem_wb_t wb_pipeline_q,
    // to csr file 
    output logic [11:0] wb_csr_addr_o,
    output logic [31:0] wb_csr_wdata_o,
    // to regfile
    output logic [4:0] wb_rd_addr_o,
    output logic [31:0] wb_rd_wdata_o
);
  logic [4:0] wb_rd_addr_masked;
  logic [31:0] wb_rd_wdata_masked;
  logic [31:0] wb_rd_wdata_comb;
  logic [11:0] wb_csr_addr_masked;

  // trap disable logic
  assign wb_rd_addr_masked = wb_pipeline_q.trap_valid ? 0 : wb_pipeline_q.rd_addr;
  assign wb_csr_addr_masked = wb_pipeline_q.trap_valid ? 0 : wb_pipeline_q.csr_addr;

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

endmodule
