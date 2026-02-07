import riscv_pkg::*;
module csr_file (
  // --------------------
  // Clock / reset
  // --------------------
  input  logic        clk_i            ,
  input  logic        rst_i            ,
  // --------------------
  // ID-stage CSR read
  // --------------------
  input  logic [11:0] id_csr_addr      ,
  output logic [31:0] csrfile_rdata    ,
  // --------------------
  // WB-stage CSR write
  // --------------------
  input  logic        wb_q_valid       ,
  input  logic        wb_q_trap_valid  ,
  input  logic        wb_q_is_csr_write,
  input  logic        wb_q_is_csr_read ,
  input  logic [11:0] wb_csr_addr      ,
  input  logic [31:0] wb_csr_wdata     ,
  input  logic [31:0] wb_trap_pc       ,
  input  logic [31:0] wb_trap_mcause   ,
  // --------------------
  // Pipeline visibility (for minstret)
  // --------------------
  input  logic        ex_q_valid       ,
  input  logic        mem_q_valid      ,
`ifdef RISCV_FORMAL
  // --------------------
  // riscv-formal CSR masks
  // --------------------
  output logic [31:0] wb_csr_rmask     ,
  output logic [31:0] wb_csr_wmask     ,
`endif
  // --------------------
  // Trap handler address output
  // --------------------
  output logic [31:0] trap_handler_addr
);

  logic [31:0] csr_mtvec_reg    ;
  logic [31:0] csr_mscratch_reg ;
  logic [31:0] csr_mepc_reg     ;
  logic [31:0] csr_mcause_reg   ;
  logic [31:0] csr_mtval_reg    ;
  logic [63:0] csr_mcycle_reg   ;
  logic [63:0] csr_minstret_reg ;
  logic [31:0] csr_mtvec_next   ;
  logic [31:0] csr_mscratch_next;
  logic [31:0] csr_mepc_next    ;
  logic [31:0] csr_mcause_next  ;
  logic [31:0] csr_mtval_next   ;
  logic [63:0] csr_mcycle_next  ;
  logic [63:0] csr_minstret_next;

  // asserted when writing to a read only register
  // rmask  bits are set if rd != 0 and addr = valid_csr_addr
  // wmask bits are set if csr_wtype != 0

  // read from the csr register file in the ID stage
  always @(*) begin
    csrfile_rdata = 0;
    case (id_csr_addr)
      CSR_ADDR_MTVEC    : csrfile_rdata = csr_mtvec_reg;
      CSR_ADDR_MSCRATCH : csrfile_rdata = csr_mscratch_reg;
      CSR_ADDR_MEPC     : csrfile_rdata = csr_mepc_reg;
      CSR_ADDR_MCAUSE   : csrfile_rdata = csr_mcause_reg;
      CSR_ADDR_MTVAL    : csrfile_rdata = csr_mtval_reg;
      CSR_ADDR_MCYCLE   : csrfile_rdata = csr_mcycle_reg[31:0];
      CSR_ADDR_MCYCLEH  : csrfile_rdata = csr_mcycle_reg[63:32];
      // since we are reading in ID stage add stages that will retire before to the count
      CSR_ADDR_MINSTRET : csrfile_rdata = csr_minstret_reg[31:0] + ex_q_valid
        + mem_q_valid + wb_q_valid;
      CSR_ADDR_MINSTRETH : csrfile_rdata = csr_minstret_reg[63:32];
      default            : ;
    endcase
  end

  // write to the csr register file in the WB stage
  // first, get the next value for each csr
  always @(*) begin
    csr_mtvec_next    = csr_mtvec_reg;
    csr_mscratch_next = csr_mscratch_reg;
    csr_mepc_next     = (wb_q_valid && wb_q_trap_valid) ? wb_trap_pc : csr_mepc_reg;
    csr_mcause_next   = (wb_q_valid && wb_q_trap_valid) ? wb_trap_mcause : csr_mcause_reg;
    csr_mtval_next    = csr_mtval_reg;
    csr_mcycle_next   = csr_mcycle_reg + 1;
    csr_minstret_next = wb_q_valid ? csr_minstret_reg + 1 : csr_minstret_reg;
    case (wb_csr_addr)
      CSR_ADDR_MTVEC    : csr_mtvec_next = wb_csr_wdata & 32'hffff_fffc;
      CSR_ADDR_MSCRATCH : csr_mscratch_next = wb_csr_wdata;
      CSR_ADDR_MEPC     : csr_mepc_next = wb_csr_wdata;
      CSR_ADDR_MCAUSE   : csr_mcause_next = wb_csr_wdata;
      CSR_ADDR_MTVAL    : csr_mtval_next = wb_csr_wdata;
      /*
      READ ONLY CSRS:
      CSR_ADDR_MCYCLE
      CSR_ADDR_MCYCLEH
      CSR_ADDR_MINSTRET
      CSR_ADDR_MINSTRETH
      */
      default           : ;
    endcase
  end

  // write the next csr value to each csr
  always @(posedge clk_i) begin
    if (rst_i) begin
      csr_mtvec_reg    <= 0;
      csr_mscratch_reg <= 0;
      csr_mepc_reg     <= 0;
      csr_mcause_reg   <= 0;
      csr_mtval_reg    <= 0;
      csr_mcycle_reg   <= 0;
      csr_minstret_reg <= 0;
    end else begin
      // use a write enable for csr registers that can be written to
      if (wb_q_is_csr_write) begin
        csr_mtvec_reg    <= csr_mtvec_next;
        csr_mscratch_reg <= csr_mscratch_next;
        csr_mepc_reg     <= csr_mepc_next;
        csr_mcause_reg   <= csr_mcause_next;
        csr_mtval_reg    <= csr_mtval_next;
      end
      csr_mcycle_reg   <= csr_mcycle_next;
      csr_minstret_reg <= csr_minstret_next;
    end
  end

  // synchronously update the trap handler register
  always @(posedge clk_i) begin
    if (rst_i) trap_handler_addr <= 0;
    else trap_handler_addr <= {csr_mtvec_reg[31:2], 2'd0};
  end

`ifdef RISCV_FORMAL
  // a csr isntruction is a read only if the destination register is not x0
  assign wb_csr_rmask = wb_q_is_csr_read ? 32'hffff_ffff : 0;
  // a csr instruction is a write if its a csrrw or if its (not a csrrw and rs1 != 0)
  assign wb_csr_wmask = wb_q_is_csr_write ? 32'hffff_ffff : 0;
`endif
endmodule