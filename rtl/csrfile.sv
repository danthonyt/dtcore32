module csrfile
  import params_pkg::*;
(
    input logic clk_i,
    input logic rst_i,
    input logic [4:0] WB_rd_addr_i,
    input logic [11:0] csr_addr_i,
    input logic WB_valid_insn_i,
    input trap_info_t WB_trap_i,
    input logic [1:0] csr_wtype_i,
    input logic [31:0] csr_woperand,
    output logic [31:0] trap_handler_addr_o,
    output logic [31:0] csr_rdata_o,
    output logic [31:0] csr_rmask_o,
    output logic [31:0] csr_wdata_o,
    output logic [31:0] csr_wmask_o
    
);
  logic [31:0] csr_mtvec;
  logic [31:0] csr_mscratch;
  logic [31:0] csr_mepc;
  logic [31:0] csr_mcause;
  logic [31:0] csr_mtval;
  logic [63:0] csr_mcycle;
  logic [63:0] csr_minstret;
  logic [31:0] csr_wdata;
  logic [31:0] csr_rdata;
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
    case (csr_addr_i)
      CSR_ADDR_MTVEC:     csr_rdata = csr_mtvec;
      CSR_ADDR_MSCRATCH:  csr_rdata = csr_mscratch;
      CSR_ADDR_MEPC:      csr_rdata = csr_mepc;
      CSR_ADDR_MCAUSE:    csr_rdata = csr_mcause;
      CSR_ADDR_MTVAL:     csr_rdata = csr_mtval;
      CSR_ADDR_MCYCLE:    csr_rdata = csr_mcycle[31:0];
      CSR_ADDR_MCYCLEH:   csr_rdata = csr_mcycle[63:32];
      CSR_ADDR_MINSTRET:  csr_rdata = csr_minstret[31:0];
      CSR_ADDR_MINSTRETH: csr_rdata = csr_minstret[63:32];
      default:            csr_rdata = 0;
    endcase
    case (csr_wtype_i)
      CSR_WRITE_RAW_VALUE:      csr_wdata = csr_woperand;
      CSR_WRITE_CLEAR_BIT_MASK: csr_wdata = (csr_rdata & ~csr_woperand);
      CSR_WRITE_SET_BIT_MASK:   csr_wdata = (csr_rdata | csr_woperand);
      default:                  csr_wdata = 0;              
    endcase

  end

  // synchronous writes
  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      csr_mepc   <= 0;
      csr_mcause <= 0;
    end else if (WB_valid_insn_i && WB_trap_i.valid) begin
      csr_mepc   <= WB_trap_i.pc;
      csr_mcause <= {WB_trap_i.is_interrupt, WB_trap_i.mcause};
    end else if (csr_addr_i == CSR_ADDR_MEPC) csr_mepc <= csr_wdata;
    else if (csr_addr_i == CSR_ADDR_MCAUSE) csr_mcause <= csr_wdata;
  end

  // the mcycle register increments on every clock cycle
  always_ff @(posedge clk_i) begin
    if (rst_i) csr_mcycle <= 0;
    else csr_mcycle <= csr_mcycle + 1;
  end

  // the minstret register increments every time a valid instruction is retired
  always_ff @(posedge clk_i) begin
    if (rst_i) csr_minstret <= 0;
    else if (WB_valid_insn_i) csr_minstret <= csr_minstret + 1;
  end

  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      csr_mtvec <= 0;
      csr_mscratch <= 0;
      csr_mtval <= 0;
    end else if (csr_addr_i == CSR_ADDR_MTVEC) csr_mtvec <= csr_wdata & 32'hffff_fffc;
    else if (csr_addr_i == CSR_ADDR_MSCRATCH) csr_mscratch <= csr_wdata;
  end

  assign trap_handler_addr_o = {csr_mtvec[31:2], 2'd0};

  // a csr isntruction is a read only if the destination register is not x0
  assign csr_rmask_o = (WB_rd_addr_i != 0) ?  32'hffff_ffff : '0;
  // a csr instruction is a write if its a csrrw or if its (not a csrrw and rs1 != 0)
  assign csr_wmask_o = (csr_wtype_i != 0)  ?  32'hffff_ffff : '0;
  assign csr_wdata_o = csr_wdata;
  assign csr_rdata_o = csr_rdata;
endmodule
