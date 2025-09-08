module csrfile
  import params_pkg::*;
(
    input logic clk_i,
    input logic rst_i,
    // to write back
`ifdef RISCV_FORMAL
    output logic [31:0] wb_csr_rmask_o,
    output logic [31:0] wb_csr_wmask_o,
    input logic [4:0] wb_rd_addr_i,
`endif
    input logic write_en_i,
    // from instruction decode
    input logic [11:0] id_csr_raddr_i,
    output logic [31:0] id_csr_rdata_o,
    // from write back

    input logic [11:0] wb_csr_waddr_i,
    input logic [31:0] wb_csr_wdata_i,

    // for counting retired instructions for minstret
    input logic wb_valid_i,
    input logic ex_valid_i,
    input logic mem_valid_i,
    // for tracking traps
    input logic wb_trap_valid_i,
    input logic [31:0] wb_trap_pc_i,
    input logic [31:0] wb_trap_mcause_i,
    output logic [31:0] trap_handler_addr_q
);
  logic [31:0] csr_mtvec_reg;
  logic [31:0] csr_mscratch_reg;
  logic [31:0] csr_mepc_reg;
  logic [31:0] csr_mcause_reg;
  logic [31:0] csr_mtval_reg;
  logic [63:0] csr_mcycle_reg;
  logic [63:0] csr_minstret_reg;
  logic [31:0] csr_mtvec_next;
  logic [31:0] csr_mscratch_next;
  logic [31:0] csr_mepc_next;
  logic [31:0] csr_mcause_next;
  logic [31:0] csr_mtval_next;
  logic [63:0] csr_mcycle_next;
  logic [63:0] csr_minstret_next;
  logic [31:0] csr_rdata;
  logic [31:0] minstret_rdata;
  //////////////////////////////////////
  //
  //  CSRS FOR MACHINE MODE
  //
  //
  ///////////////////////////////////////

  // asserted when writing to a read only register
  // rmask  bits are set if rd != 0 and addr = valid_csr_addr
  // wmask bits are set if csr_wtype != 0
  assign minstret_rdata = csr_minstret_reg[31:0] + 
      {31'd0, ex_valid_i} + {31'd0, mem_valid_i} + {31'd0, wb_valid_i};

  always_comb begin
    csr_rdata = 0;
    case (id_csr_raddr_i)
      CSR_ADDR_MTVEC: csr_rdata = csr_mtvec_reg;
      CSR_ADDR_MSCRATCH: csr_rdata = csr_mscratch_reg;
      CSR_ADDR_MEPC: csr_rdata = csr_mepc_reg;
      CSR_ADDR_MCAUSE: csr_rdata = csr_mcause_reg;
      CSR_ADDR_MTVAL: csr_rdata = csr_mtval_reg;
      CSR_ADDR_MCYCLE: csr_rdata = csr_mcycle_reg[31:0];
      CSR_ADDR_MCYCLEH: csr_rdata = csr_mcycle_reg[63:32];
      // since we are reading in ID stage add stages that will retire before to the count
      CSR_ADDR_MINSTRET: csr_rdata = minstret_rdata;
      CSR_ADDR_MINSTRETH: csr_rdata = csr_minstret_reg[63:32];
      default: ;
    endcase
  end

  always_comb begin
    csr_mtvec_next = csr_mtvec_reg;
    csr_mscratch_next = csr_mscratch_reg;
    csr_mepc_next = (wb_valid_i && wb_trap_valid_i) ? wb_trap_pc_i : csr_mepc_reg;
    csr_mcause_next = (wb_valid_i && wb_trap_valid_i) ? wb_trap_mcause_i : csr_mcause_reg;
    csr_mtval_next = csr_mtval_reg;
    csr_mcycle_next = csr_mcycle_reg + 1;
    csr_minstret_next = wb_valid_i ? csr_minstret_reg + 1 : csr_minstret_reg;
    case (wb_csr_waddr_i)
      CSR_ADDR_MTVEC:    csr_mtvec_next = wb_csr_wdata_i & 32'hffff_fffc;
      CSR_ADDR_MSCRATCH: csr_mscratch_next = wb_csr_wdata_i;
      CSR_ADDR_MEPC:     csr_mepc_next = wb_csr_wdata_i;
      CSR_ADDR_MCAUSE:   csr_mcause_next = wb_csr_wdata_i;
      CSR_ADDR_MTVAL:    csr_mtval_next = wb_csr_wdata_i;
      // read only CSR_ADDR_MCYCLE:    csr_mcycle_next[31:0] = wb_csr_wdata_i;
      // read only CSR_ADDR_MCYCLEH:   csr_mcycle_next[63:32] = wb_csr_wdata_i;
      // read only CSR_ADDR_MINSTRET:  csr_minstret_next[31:0] = wb_csr_wdata_i;
      // read only CSR_ADDR_MINSTRETH: csr_minstret_next[63:32] = wb_csr_wdata_i;
      default:           ;
    endcase
  end

  // csr writes
  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      csr_mtvec_reg <= 0;
      csr_mscratch_reg <= 0;
      csr_mepc_reg <= 0;
      csr_mcause_reg <= 0;
      csr_mtval_reg <= 0;
      csr_mcycle_reg <= 0;
      csr_minstret_reg <= 0;
    end else begin
      // use a write enable for csr registers that can be written to
      if (write_en_i) begin
        csr_mtvec_reg <= csr_mtvec_next;
        csr_mscratch_reg <= csr_mscratch_next;
        csr_mepc_reg <= csr_mepc_next;
        csr_mcause_reg <= csr_mcause_next;
        csr_mtval_reg <= csr_mtval_next;
      end
      csr_mcycle_reg   <= csr_mcycle_next;
      csr_minstret_reg <= csr_minstret_next;
    end
  end

  // synchronously update the trap handler register
  always_ff @(posedge clk_i) begin
    if (rst_i) trap_handler_addr_q <= 0;
    else trap_handler_addr_q <= {csr_mtvec_reg[31:2], 2'd0};
  end

  assign id_csr_rdata_o = csr_rdata;
`ifdef RISCV_FORMAL
  // a csr isntruction is a read only if the destination register is not x0
  assign wb_csr_rmask_o = (wb_rd_addr_i != 0) ? 32'hffff_ffff : '0;
  // a csr instruction is a write if its a csrrw or if its (not a csrrw and rs1 != 0)
  assign wb_csr_wmask_o = (wb_csr_waddr_i != 0) ? 32'hffff_ffff : '0;
`endif

endmodule
