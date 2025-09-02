module pipeline_reg
  import params_pkg::*;
#(
    type pipeline_t = if_id_t,
    parameter pipeline_t RESET_PIPELINE = '{insn: 32'h00000013, default: 0}
) (
    input logic clk_i,
    input logic rst_i,
    input logic stall_i,
    input logic flush_i,
    input logic prev_stage_stall_i,
    input pipeline_t pipeline_d,
    output pipeline_t pipeline_q
);

  always_ff @(posedge clk_i) begin
    if (rst_i || flush_i) begin
      pipeline_q <= RESET_PIPELINE;
    end else if (!stall_i) begin
      if (!pipeline_d.valid || prev_stage_stall_i) begin
        pipeline_q <= RESET_PIPELINE;
      end else begin
        pipeline_q <= pipeline_d;
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
  assert property (rst_i || flush_i |-> ##1 pipeline_q == RESET_PIPELINE);
  assert property (disable iff (rst_i || flush_i) stall_i |-> ##1 $stable(pipeline_q));
  assert property (disable iff (rst_i || flush_i || stall_i) !pipeline_d.valid |-> ##1 pipeline_q == RESET_PIPELINE);

`endif
endmodule
