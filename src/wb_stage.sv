module wb_stage(
    input logic [31:0] wb_q_trap_mcause,
    input logic [31:0] wb_q_trap_pc,
    input logic [4:0] wb_q_rd_addr,
    input logic [31:0] wb_q_rd_wdata,
    input logic [11:0] wb_q_csr_addr,
    input logic [31:0] wb_q_csr_wdata,
    output logic [31:0] wb_trap_mcause,
    output logic [31:0] wb_trap_pc,
    output logic [4:0] wb_rd_addr,
    output logic [31:0] wb_rd_wdata,
    output logic [11:0] wb_csr_addr,
    output logic [31:0] wb_csr_wdata
);

    assign wb_trap_mcause = wb_q_trap_mcause;
    assign wb_trap_pc     = wb_q_trap_pc;
    assign wb_rd_addr     = wb_q_rd_addr;
    assign wb_rd_wdata    = wb_q_rd_wdata;
    assign wb_csr_addr    = wb_q_csr_addr;
    assign wb_csr_wdata   = wb_q_csr_wdata;
endmodule
