module if_id_reg
  import params_pkg::*;
(
    input  logic   clk_i,
    input  logic   rst_i,
    input  logic   if_id_stall_i,
    input  logic   if_id_flush_i,
    input  if_id_t if_pipeline_d,
    output if_id_t id_pipeline_q
);
  if_id_t reset_if_id;
  always_comb begin
    reset_if_id              = '0;  // zero all simple/packed fields
    reset_if_id.insn         = 32'h00000013;  // NOP
  end

  always_ff @(posedge clk_i) begin
    if (rst_i || if_id_flush_i) begin
      id_pipeline_q <= reset_if_id;
    end else if (!if_id_stall_i) begin
      if (!if_pipeline_d.valid) begin
        id_pipeline_q <= reset_if_id;
      end else begin
        id_pipeline_q <= if_pipeline_d;
      end
    end
  end


  /******************************************/
  //
  //    FORMAL VERIFICATION
  //
  /******************************************/
`ifdef FORMAL
  default clocking @(posedge clk_i);
  endclocking
  initial assume (rst_i);
  assert property (rst_i || if_id_flush_i |-> ##1 id_pipeline_q == reset_if_id);
  assert property (disable iff (rst_i || if_id_flush_i) if_id_stall_i |-> ##1 $stable(id_pipeline_q));
  assert property (disable iff (rst_i || if_id_flush_i || if_id_stall_i) !if_pipeline_d.valid |-> ##1 id_pipeline_q == reset_if_id);

`endif
endmodule
