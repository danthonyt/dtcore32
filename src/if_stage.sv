import riscv_pkg::*;
module if_stage (
  // Clock & Reset
  input  logic        clk_i,
  input  logic        rst_i,

  // Pipeline control
  input  logic        if_id_flush,
  input  logic        if_id_stall,

  // WB / MEM stage signals for mispredicts & traps
  input  logic        wb_q_trap_valid,
  input  logic [31:0] trap_handler_addr,
  input  logic        mem_btaken_mispredict,
  input  logic        mem_bntaken_mispredict,
  input  logic [31:0] mem_q_pc_plus_4,
  input  logic [31:0] mem_q_jaddr,
  input  logic        mem_q_jump_taken,
  input  logic        mem_q_is_branch,
  input  logic        id_predict_btaken,
  input  logic [31:0] id_branch_addr,

  // Instruction memory interface
  input  logic [31:0] imem_rdata_i,
  output logic [31:0] imem_addr_o,

  // Pipeline outputs
  output logic [31:0] if_d_pc,
  output logic [31:0] if_d_pc_plus_4,
  output logic [31:0] if_d_insn,
  output logic        if_d_valid,
  output logic [31:0] next_pc,
  output logic imem_rdata_valid
`ifdef RISCV_FORMAL
  ,
  // RVFI / formal signals
  output logic        if_d_intr
`endif
);


logic [31:0] imem_addr_q;
logic [31:0] if_buf_pc;
logic [31:0] if_insn_buf;
logic imem_buf_valid;
  // send read address to the instruction memory
  always @(posedge clk_i)
    begin
      if (rst_i)
        begin
          imem_addr_o      <= RESET_PC;
          imem_rdata_valid <= 0;
        end
      else if (if_id_flush) begin
        imem_addr_o      <= next_pc;
        imem_rdata_valid <= 0;
      end
      else if (!if_id_stall)
        begin
          imem_addr_o      <= next_pc;
          imem_rdata_valid <= 1;
        end
    end


  // registers imem address to stay cycle aligned with imem rdata
  // imem reads have 1 cycle latency
  always @(posedge clk_i)
    begin
      if (rst_i) begin
        imem_addr_q <= RESET_PC;
      end else begin
        imem_addr_q <= imem_addr_o;
      end
    end

  // buffer
  always @(posedge clk_i)
    begin
      if (rst_i)
        begin
          imem_buf_valid <= 0;
        end
      else if (if_id_flush) begin
        imem_buf_valid <= 0;
      end
      else if (!if_id_stall)
        begin
          imem_buf_valid <= 0;
        end
      // When entering a stall, buffer the instruction memory read data.
      // When first leaving a stall, use the buffered data instead. This
      // is to avoid losing instruction data when entering a stall.
      else if (if_id_stall && !imem_buf_valid)
        begin
          if_insn_buf    <= imem_rdata_i;
          imem_buf_valid <= 1;
          if_buf_pc      <= imem_addr_q;
        end
    end

  always @(*)
    begin
      // jump to trap handler if a trap instruction commits
      // else if a branch taken and mispredicted jump to mem.pc + 4
      // else if a branch not taken and mispredicted OR a jump instruction
      // jump to mem.jaddr
      // else if a branch taken is predicted jump to that address
      // else increment pc by 4
      next_pc = wb_q_trap_valid ? trap_handler_addr :
        mem_btaken_mispredict ? mem_q_pc_plus_4 :
        mem_bntaken_mispredict ? mem_q_jaddr :
        mem_q_jump_taken && !mem_q_is_branch ? mem_q_jaddr :
        id_predict_btaken ? id_branch_addr :
        imem_addr_o + 4;
      if_d_pc        = imem_buf_valid ? if_buf_pc : imem_addr_q;
      if_d_pc_plus_4 = if_d_pc + 4;
      if_d_insn      = imem_buf_valid ? if_insn_buf : imem_rdata_i;
      if_d_valid     = imem_rdata_valid;
    end

`ifdef RISCV_FORMAL
  reg if_intr_d ;
  reg if_intr_q ;
  reg if_intr_qq;
  always @(posedge clk_i)
    begin
      if (rst_i)
        begin
          if_intr_q  <= 0;
          if_intr_qq <= 0;
        end
      else if (if_id_flush)
        begin
          if_intr_q  <= 0;
          if_intr_qq <= 0;
        end
      else if (!if_id_stall)
        begin
          if_intr_q  <= if_intr_d;
          if_intr_qq <= if_intr_q;
        end
    end
  always @(*)
    begin
      if_d_intr = if_intr_qq;
      if_intr_d = wb_q_trap_valid;
    end
`endif

endmodule