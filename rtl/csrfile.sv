module csrfile
  import params_pkg::*;
(
    input logic CLK,
    input logic RST,
    input logic [4:0] WB_RD_ADDR,
    input logic [11:0] CSR_RADDR,
    input logic [11:0] CSR_WADDR,
    input logic [31:0] CSR_WDATA,
    input logic WB_VALID_INSN,
    input trap_info_t WB_TRAP,
    input logic EX_VALID,
    input logic MEM_VALID,
    input logic WB_VALID,
    output logic [31:0] TRAP_HANDLER_ADDR,
    output logic [31:0] CSR_RDATA_REG,
    output logic [31:0] CSR_RMASK,
    output logic [31:0] CSR_WMASK

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
  logic [31:0] csr_wdata;
  logic [31:0] csr_rdata;
  logic [31:0] csr_rdata_reg;
  //////////////////////////////////////
  //
  //  CSRS FOR MACHINE MODE
  //
  //
  ///////////////////////////////////////

  // asserted when writing to a read only register
  // rmask  bits are set if rd != 0 and addr = valid_csr_addr
  // wmask bits are set if csr_wtype != 0

  always_comb begin
    csr_rdata = 0;
    case (CSR_RADDR)
      CSR_ADDR_MTVEC:     csr_rdata = csr_mtvec_reg;
      CSR_ADDR_MSCRATCH:  csr_rdata = csr_mscratch_reg;
      CSR_ADDR_MEPC:      csr_rdata = csr_mepc_reg;
      CSR_ADDR_MCAUSE:    csr_rdata = csr_mcause_reg;
      CSR_ADDR_MTVAL:     csr_rdata = csr_mtval_reg;
      CSR_ADDR_MCYCLE:    csr_rdata = csr_mcycle_reg[31:0];
      CSR_ADDR_MCYCLEH:   csr_rdata = csr_mcycle_reg[63:32];
      // since we are reading in ID stage add stages that will retire before to the count
      CSR_ADDR_MINSTRET:  csr_rdata = csr_minstret_reg[31:0] + EX_VALID + MEM_VALID + WB_VALID;
      CSR_ADDR_MINSTRETH: csr_rdata = csr_minstret_reg[63:32];
      default:            ;
    endcase
  end

  always_comb begin
    csr_mtvec_next = csr_mtvec_reg;
    csr_mscratch_next = csr_mscratch_reg;
    csr_mepc_next = (WB_VALID_INSN && WB_TRAP.valid) ? WB_TRAP.pc : csr_mepc_reg;
    csr_mcause_next = (WB_VALID_INSN && WB_TRAP.valid) ? {WB_TRAP.is_interrupt, WB_TRAP.mcause} : csr_mcause_reg;
    csr_mtval_next = csr_mtval_reg;
    csr_mcycle_next = csr_mcycle_reg + 1;
    csr_minstret_next = WB_VALID_INSN ? csr_minstret_reg + 1 : csr_minstret_reg;
    case (CSR_WADDR)
      CSR_ADDR_MTVEC:     csr_mtvec_next = CSR_WDATA & 32'hffff_fffc;
      CSR_ADDR_MSCRATCH:  csr_mscratch_next = CSR_WDATA;
      CSR_ADDR_MEPC:      csr_mepc_next = CSR_WDATA;
      CSR_ADDR_MCAUSE:    csr_mcause_next = CSR_WDATA;
      CSR_ADDR_MTVAL:     csr_mtval_next = CSR_WDATA;
      // read only CSR_ADDR_MCYCLE:    csr_mcycle_next[31:0] = CSR_WDATA;
      // read only CSR_ADDR_MCYCLEH:   csr_mcycle_next[63:32] = CSR_WDATA;
      // read only CSR_ADDR_MINSTRET:  csr_minstret_next[31:0] = CSR_WDATA;
      // read only CSR_ADDR_MINSTRETH: csr_minstret_next[63:32] = CSR_WDATA;
      default:            ;
    endcase
  end
  // csr read
  always_ff @(posedge CLK) begin
    if (RST) begin
      csr_rdata_reg <= 0;
    end else begin
      csr_rdata_reg <= csr_rdata;
    end
  end

  // csr writes
  always_ff @(posedge CLK) begin
    if (RST) begin
      csr_mtvec_reg <= 0;
      csr_mscratch_reg <= 0;
      csr_mepc_reg <= 0;
      csr_mcause_reg <= 0;
      csr_mtval_reg <= 0;
      csr_mcycle_reg <= 0;
      csr_minstret_reg <= 0;
    end else begin
      csr_mtvec_reg <= csr_mtvec_next;
      csr_mscratch_reg <= csr_mscratch_next;
      csr_mepc_reg <= csr_mepc_next;
      csr_mcause_reg <= csr_mcause_next;
      csr_mtval_reg <= csr_mtval_next;
      csr_mcycle_reg <= csr_mcycle_next;
      csr_minstret_reg <= csr_minstret_next;
    end
  end

  // synchronously update the trap handler register
  always_ff @(posedge CLK) begin
    if (RST) TRAP_HANDLER_ADDR <= 0;
    else TRAP_HANDLER_ADDR <= {csr_mtvec_reg[31:2], 2'd0};
  end

  // a csr isntruction is a read only if the destination register is not x0
  assign CSR_RMASK = (WB_RD_ADDR != 0) ? 32'hffff_ffff : '0;
  // a csr instruction is a write if its a csrrw or if its (not a csrrw and rs1 != 0)
  assign CSR_WMASK = (CSR_WADDR != 0) ? 32'hffff_ffff : '0;
  assign CSR_RDATA_REG = csr_rdata_reg;
endmodule
