module if_stage
  import params_pkg::*;
#(
    parameter RESET_PC = 0
) (
    input logic clk_i,
    input logic rst_i,
    input logic if_id_stall_i,
    input logic if_id_flush_i,
    input logic [31:0] imem_rdata_i,
    input logic ex_is_pc_redirect_i,
    input logic [31:0] ex_pc_target_i,
    input logic wb_trap_valid_i,
    input logic [31:0] trap_handler_addr_i,
    output logic [31:0] imem_addr_o,
    output if_id_t if_pipeline_d
);
  logic if_intr_d;
  logic if_intr_q;
  logic [31:0] next_pc;
  logic if_intr_qq;
  logic [31:0] if_pc_qq;
  logic if_valid_qq;
  logic imem_buf_valid;
  logic [31:0] if_insn_buf;
  logic [31:0] if_pc_q;
  logic [31:0] if_pc;

  // On a trap, the next pc is the trap handler address,
  // else if a jump or branch, next pc is the specified jump/branch address
  // else next pc is the previous pc incremented by 4
  assign next_pc = wb_trap_valid_i ? trap_handler_addr_i : 
  ex_is_pc_redirect_i ?  ex_pc_target_i : if_pc_q + 4;
  // indicates the first instruction entering the trap handler
  assign if_intr_d = wb_trap_valid_i;

  // send read address to the instruction memory
  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      if_pc_q   <= RESET_PC;
      if_intr_q <= 0;
    end else if (!if_id_stall_i) begin
      if_pc_q   <= next_pc;
      if_intr_q <= if_intr_d;
    end
  end

  // register the instruction memory input  
  // so it aligns with the instruction memory 
  // read data
  always_ff @(posedge clk_i) begin
    if (rst_i || if_id_flush_i) begin
      if_valid_qq <= 0;
      if_pc_qq <= 'x;
      if_intr_qq <= 'x;
    end else if (!if_id_stall_i) begin
      if_valid_qq <= 1;
      if_pc_qq <= if_pc_q;
      if_intr_qq <= if_intr_q;
    end
  end

  // When entering a stall, buffer the instruction memory read data.
  // When first leaving a stall, use the buffered data instead. This 
  // is to avoid losing instruction data when entering a stall.
  always_ff @(posedge clk_i) begin
    if (rst_i || if_id_flush_i) begin
      if_insn_buf <= 'x;
      imem_buf_valid <= 0;
    end else if (if_id_stall_i && !imem_buf_valid) begin
      if_insn_buf <= imem_rdata_i;
      imem_buf_valid <= 1;
    end else if (!if_id_stall_i) begin
      if_insn_buf <= 'x;
      imem_buf_valid <= 0;
    end
  end

  assign imem_addr_o = if_pc_q;
  assign if_insn = imem_buf_valid ? if_insn_buf : imem_rdata_i;

  always_comb begin
    if_pipeline_d.pc = if_pc_qq;
    if_pipeline_d.pc_plus_4 = if_pc_qq + 4;
    if_pipeline_d.insn = if_insn;
    if_pipeline_d.valid = if_valid_qq;
    if_pipeline_d.intr = if_intr_qq;
  end
  /*
  assign CPU_FETCH_WBM_CYC_O = !if_id_stall_i;
  assign CPU_FETCH_WBM_STB_O = !if_id_stall_i;
  */

  /******************************************/
  //
  //    FORMAL VERIFICATION
  //
  /******************************************/
`ifdef FORMAL
  default clocking @(posedge clk_i);
  endclocking
  initial assume (rst_i);
  // reset conditions :
  // invalid buffer
  // invalid instruction
  // pc is reset pc
  assert property (rst_i || if_id_flush_i |-> ##1 !imem_buf_valid);
  assert property (rst_i || if_id_flush_i |-> ##1 !if_valid_qq);
  assert property (rst_i |-> ##1 if_pc_q == RESET_PC);
  // buffer is valid during a stall
  assert property (disable iff (rst_i || if_id_flush_i) if_id_stall_i |-> ##[1:$] imem_buf_valid);
  // buffer is invalid after leaving stall
  assert property (disable iff (rst_i || if_id_flush_i) $fell(
      if_id_stall_i
  ) |-> ##1 !imem_buf_valid);
  //
  assert property (wb_trap_valid_i |-> if_intr_d);
  // next pc is the trap handler address on a trap
  assert property (wb_trap_valid_i |-> next_pc == trap_handler_addr_i);
  // next pc is the jump address on jump/branch
  assert property (!wb_trap_valid_i && ex_is_pc_redirect_i |-> next_pc == ex_pc_target_i);
  // next pc is the pc + 4 otherwise
  assert property (!wb_trap_valid_i && !ex_is_pc_redirect_i |-> next_pc == (if_pc_q + 4));
`endif

endmodule
