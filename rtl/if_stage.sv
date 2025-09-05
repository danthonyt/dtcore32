module if_stage
  import params_pkg::*;
#(
    parameter RESET_PC = 0
) (
    input logic clk_i,
    input logic rst_i,
    input logic if_id_stall_i,
    input logic if_id_flush_i,
    // from instruction memory 
    input logic [31:0] imem_rdata_i,
    // to instruction memory
    output logic [31:0] imem_addr_o,
    // from instruction execute stage
    input logic ex_is_pc_redirect_i,
    input logic [31:0] ex_pc_target_i,
    // from writeback stage
    input logic wb_trap_valid_i,
    // from csr file
    input logic [31:0] trap_handler_addr_i,
    // pipeline
    output if_id_t if_pipeline_d
);

  //*****************************************************************
  //
  //
  // SIGNALS
  //
  //
  //*****************************************************************
  logic [31:0] wb_trap_valid_q;
  logic [31:0] pc_incr;
  logic [31:0] pc_incr_q;
  logic [31:0] ex_pc_target_q;
  logic [31:0] trap_handler_addr_q;
  logic ex_is_pc_redirect_q;
  logic [31:0] if_pc_qq;
  logic if_valid_qq;
  logic imem_buf_valid;
  logic [31:0] if_insn;
  logic [31:0] if_insn_buf;
  logic if_flush_q;
  logic if_stall_q;
  //*****************************************************************
  //
  //
  // ASSIGNMENTS
  //
  //
  //*****************************************************************
  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      if_stall_q <= 0;
    end else begin
      if_stall_q <= if_id_stall_i;
    end
  end
  // On a trap, the next pc is the trap handler address,
  // else if a jump or branch, next pc is the specified jump/branch address
  // else next pc is the previous pc incremented by 4
  assign imem_addr_o = wb_trap_valid_q ? trap_handler_addr_q : 
  ex_is_pc_redirect_q ?  ex_pc_target_q : pc_incr_q;
  assign pc_incr = imem_addr_o + 4;
  // send read address to the instruction memory
  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      pc_incr_q <= RESET_PC;
      ex_is_pc_redirect_q <= 0;
      trap_handler_addr_q <= 0;
      wb_trap_valid_q <= 0;
      ex_pc_target_q <= 0;
    end else if (!if_id_stall_i) begin
      pc_incr_q <= pc_incr;
      ex_is_pc_redirect_q <= ex_is_pc_redirect_i;
      trap_handler_addr_q <= trap_handler_addr_i;
      wb_trap_valid_q <= wb_trap_valid_i;
      ex_pc_target_q <= ex_pc_target_i;
    end
  end

  // register the instruction memory input  
  // so it aligns with the instruction memory 
  // read data
  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      if_valid_qq <= 0;
      if_pc_qq <= 'x;
      if_flush_q <= 0;
    end else if (!if_id_stall_i) begin
      if_valid_qq <= 1;
      if_pc_qq <= imem_addr_o;
      if_flush_q <= if_id_flush_i;
    end
  end

  // When entering a stall, buffer the instruction memory read data.
  // When first leaving a stall, use the buffered data instead. This 
  // is to avoid losing instruction data when entering a stall.
  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      if_insn_buf <= 'x;
      imem_buf_valid <= 0;
    end else begin
      if (if_id_stall_i && !imem_buf_valid) begin
        if_insn_buf <= imem_rdata_i;
        imem_buf_valid <= 1;
      end else if (!if_id_stall_i) begin
        if_insn_buf <= 'x;
        imem_buf_valid <= 0;
      end
    end
  end
  assign if_insn = imem_buf_valid ? if_insn_buf : imem_rdata_i;

  always_comb begin
    if_pipeline_d.stall = if_stall_q || if_id_stall_i;
    if_pipeline_d.flush = if_flush_q || if_id_flush_i;
    if_pipeline_d.pc = if_pc_qq;
    if_pipeline_d.pc_plus_4 = if_pc_qq + 4;
    if_pipeline_d.insn = if_insn;
    if_pipeline_d.valid = if_valid_qq;
  end
  //*****************************************************************
  //
  //
  // RISCV_FORMAL
  //
  //
  //*****************************************************************
`ifdef RISCV_FORMAL
  logic if_intr_d;
  logic if_intr_q;
  logic if_intr_qq;
  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      if_intr_q <= 0;
    end else if (!if_id_stall_i) begin
      if_intr_q <= if_intr_d;
    end
  end
  always_ff @(posedge clk_i) begin
    if (rst_i || if_id_flush_i) begin
      if_intr_qq <= 0;
    end else if (!if_id_stall_i) begin
      if_intr_qq <= if_intr_q;
    end
  end
  always_comb begin
    if_pipeline_d.intr = if_intr_qq;
    if_intr_d = wb_trap_valid_i;
  end
`endif


endmodule
