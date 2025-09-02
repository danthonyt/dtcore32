module id_ex_reg
  import params_pkg::*;
(
    input  logic   clk_i,
    input  logic   rst_i,
    input  logic   id_ex_stall_i,
    input  logic   id_ex_flush_i,
    input  id_ex_t id_pipeline_d,
    output id_ex_t ex_pipeline_q
);
  id_ex_t reset_id_ex;
  always_comb begin
    reset_id_ex              = '0;  // zero all simple/packed fields
    reset_id_ex.carried_trap = '0;  // zero the nested trap struct
    reset_id_ex.insn         = 32'h00000013;  // NOP
  end

  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      ex_pipeline_q <= reset_id_ex;
    end else if (id_ex_flush_i) begin
      ex_pipeline_q <= reset_id_ex;
    end else if (!id_ex_stall_i) begin
      if (!id_pipeline_d.valid) begin
        ex_pipeline_q <= reset_id_ex;
      end else begin
        ex_pipeline_q <= id_pipeline_d;
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
  assert property (rst_i || id_ex_flush_i |-> ##1 ex_pipeline_q == reset_id_ex);
  assert property (disable iff (rst_i || id_ex_flush_i) id_ex_stall_i |-> ##1 $stable(
      ex_pipeline_q
  ));
  assert property (disable iff (rst_i || id_ex_flush_i || id_ex_stall_i) !id_pipeline_d.valid |-> ##1 ex_pipeline_q == reset_id_ex);

`endif
endmodule
