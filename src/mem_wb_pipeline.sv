import riscv_pkg::*;
module mem_wb_pipeline (
  input  logic       clk_i,
  input  logic       rst_i,
  input  logic       mem_wb_flush,
  input  logic       mem_wb_stall,
  input  logic       ex_mem_stall,
  input  logic       mem_d_valid,
  input  logic [4:0]  mem_d_rd_addr,
  input  logic [11:0] mem_d_csr_addr,
  input  logic [31:0] mem_d_csr_wdata,
  input  logic [31:0] mem_d_rd_wdata,
  input  logic [31:0] mem_d_pc_plus_4,
  input  logic        mem_d_is_csr_write,
  input  logic        mem_d_is_csr_read,
  input  logic        mem_d_is_rd_write,
  input  logic        mem_d_trap_valid,
  input  logic [31:0] mem_d_trap_mcause,
  input  logic [31:0] mem_d_trap_pc,
`ifdef RISCV_FORMAL
  input  logic [31:0] mem_d_pc,
  input  logic [31:0] mem_d_next_pc,
  input  logic [31:0] mem_d_insn,
  input  logic        mem_d_intr,
  input  logic [31:0] mem_d_csr_rdata,
  input  logic [31:0] mem_d_mem_addr,
  input  logic [31:0] mem_d_load_rdata,
  input  logic [4:0]  mem_d_rs1_addr,
  input  logic [4:0]  mem_d_rs2_addr,
  input  logic [31:0] mem_d_rs1_rdata,
  input  logic [31:0] mem_d_rs2_rdata,
  input  logic [3:0] mem_d_load_rmask,
  input  logic [3:0] mem_d_store_wmask,
  input  logic [31:0] mem_d_store_wdata,
  input  logic [31:0] mem_d_trap_insn,
  input  logic [31:0] mem_d_trap_next_pc,
  input  logic [4:0]  mem_d_trap_rs1_addr,
  input  logic [4:0]  mem_d_trap_rs2_addr,
  input  logic [4:0]  mem_d_trap_rd_addr,
  input  logic [31:0] mem_d_trap_rs1_rdata,
  input  logic [31:0] mem_d_trap_rs2_rdata,
  input  logic [31:0] mem_d_trap_rd_wdata,
  output logic [31:0] wb_q_pc,
  output logic [31:0] wb_q_next_pc,
  output logic [31:0] wb_q_insn,
  output logic        wb_q_intr,
  output logic [31:0] wb_q_csr_rdata,
  output logic [31:0] wb_q_mem_addr,
  output logic [31:0] wb_q_load_rdata,
  output logic [4:0]  wb_q_rs1_addr,
  output logic [4:0]  wb_q_rs2_addr,
  output logic [31:0] wb_q_rs1_rdata,
  output logic [31:0] wb_q_rs2_rdata,
  output logic [3:0] wb_q_load_rmask,
  output logic [3:0] wb_q_store_wmask,
  output logic [31:0] wb_q_store_wdata,
  output logic [31:0] wb_q_trap_insn,
  output logic [31:0] wb_q_trap_next_pc,
  output logic [4:0]  wb_q_trap_rs1_addr,
  output logic [4:0]  wb_q_trap_rs2_addr,
  output logic [4:0]  wb_q_trap_rd_addr,
  output logic [31:0] wb_q_trap_rs1_rdata,
  output logic [31:0] wb_q_trap_rs2_rdata,
  output logic [31:0] wb_q_trap_rd_wdata,
`endif
  output logic       wb_q_valid,
  output logic [4:0]  wb_q_rd_addr,
  output logic [11:0] wb_q_csr_addr,
  output logic [31:0] wb_q_csr_wdata,
  output logic [31:0] wb_q_rd_wdata,
  output logic [31:0] wb_q_pc_plus_4,
  output logic        wb_q_is_csr_write,
  output logic        wb_q_is_csr_read,
  output logic        wb_q_is_rd_write,
  output logic        wb_q_trap_valid,
  output logic [31:0] wb_q_trap_mcause,
  output logic [31:0] wb_q_trap_pc
);

always_ff @(posedge clk_i) begin
    if (rst_i || mem_wb_flush || (!mem_wb_stall && ex_mem_stall)) begin
      // clear MEM/WB pipeline registers
      wb_q_valid     <= 0;
      wb_q_rd_addr   <= 0;
      wb_q_csr_addr  <= 0;
      wb_q_csr_wdata <= 0;
      wb_q_rd_wdata  <= 0;
      wb_q_pc_plus_4 <= 0;

      wb_q_is_csr_write <= 0;
      wb_q_is_csr_read  <= 0;
      wb_q_is_rd_write  <= 0;

      wb_q_trap_valid  <= 0;
      wb_q_trap_mcause <= 0;
      wb_q_trap_pc     <= 0;

`ifdef RISCV_FORMAL
      wb_q_pc             <= 0;
      wb_q_next_pc        <= 0;
      wb_q_insn           <= 0;
      wb_q_intr           <= 0;
      wb_q_csr_rdata      <= 0;
      wb_q_mem_addr       <= 0;
      wb_q_load_rdata     <= 0;
      wb_q_rs1_addr       <= 0;
      wb_q_rs2_addr       <= 0;
      wb_q_rs1_rdata      <= 0;
      wb_q_rs2_rdata      <= 0;
      wb_q_load_rmask     <= 0;
      wb_q_store_wmask    <= 0;
      wb_q_store_wdata    <= 0;
      wb_q_trap_insn      <= 0;
      wb_q_trap_next_pc   <= 0;
      wb_q_trap_rs1_addr  <= 0;
      wb_q_trap_rs2_addr  <= 0;
      wb_q_trap_rd_addr   <= 0;
      wb_q_trap_rs1_rdata <= 0;
      wb_q_trap_rs2_rdata <= 0;
      wb_q_trap_rd_wdata  <= 0;
`endif
    end else if (!mem_wb_stall) begin
      // propagate MEM stage outputs to WB stage
      wb_q_valid     <= mem_d_valid;
      wb_q_rd_addr   <= mem_d_rd_addr;
      wb_q_csr_addr  <= mem_d_csr_addr;
      wb_q_csr_wdata <= mem_d_csr_wdata;
      wb_q_rd_wdata  <= mem_d_rd_wdata;
      wb_q_pc_plus_4 <= mem_d_pc_plus_4;

      wb_q_is_csr_write <= mem_d_is_csr_write;
      wb_q_is_csr_read  <= mem_d_is_csr_read;
      wb_q_is_rd_write  <= mem_d_is_rd_write;

      wb_q_trap_valid  <= mem_d_trap_valid;
      wb_q_trap_mcause <= mem_d_trap_mcause;
      wb_q_trap_pc     <= mem_d_trap_pc;

`ifdef RISCV_FORMAL
      wb_q_pc             <= mem_d_pc;
      wb_q_next_pc        <= mem_d_next_pc;
      wb_q_insn           <= mem_d_insn;
      wb_q_intr           <= mem_d_intr;
      wb_q_csr_rdata      <= mem_d_csr_rdata;
      wb_q_mem_addr       <= mem_d_mem_addr;
      wb_q_load_rdata     <= mem_d_load_rdata;
      wb_q_rs1_addr       <= mem_d_rs1_addr;
      wb_q_rs2_addr       <= mem_d_rs2_addr;
      wb_q_rs1_rdata      <= mem_d_rs1_rdata;
      wb_q_rs2_rdata      <= mem_d_rs2_rdata;
      wb_q_load_rmask     <= mem_d_load_rmask;
      wb_q_store_wmask    <= mem_d_store_wmask;
      wb_q_store_wdata    <= mem_d_store_wdata;
      wb_q_trap_insn      <= mem_d_trap_insn;
      wb_q_trap_next_pc   <= mem_d_trap_next_pc;
      wb_q_trap_rs1_addr  <= mem_d_trap_rs1_addr;
      wb_q_trap_rs2_addr  <= mem_d_trap_rs2_addr;
      wb_q_trap_rd_addr   <= mem_d_trap_rd_addr;
      wb_q_trap_rs1_rdata <= mem_d_trap_rs1_rdata;
      wb_q_trap_rs2_rdata <= mem_d_trap_rs2_rdata;
      wb_q_trap_rd_wdata  <= mem_d_trap_rd_wdata;
`endif
    end
  end
  
endmodule
