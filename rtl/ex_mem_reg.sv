module ex_mem_reg
  import params_pkg::*;
(
    input logic clk_i,
    input logic rst_i,
    input logic ex_mem_stall_i,
    input logic ex_mem_flush_i,
    input ex_mem_t ex_pipeline_d,
    output ex_mem_t mem_pipeline_q
);
  ex_mem_t reset_ex_mem;
  always_comb begin
    reset_ex_mem              = '0;  // zero all simple/packed fields
    reset_ex_mem.carried_trap = '0;  // zero the nested trap struct
    reset_ex_mem.insn         = 32'h00000013;  // NOP
  end
  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      mem_pipeline_q <= reset_ex_mem;
    end else if (ex_mem_flush_i) begin
      mem_pipeline_q <= reset_ex_mem;
    end else if (!ex_mem_stall_i) begin
      if (!ex_pipeline_d.valid) begin
        mem_pipeline_q <= reset_ex_mem;
      end else begin
        mem_pipeline_q <= ex_pipeline_d;
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
  assert property (rst_i || ex_mem_flush_i |-> ##1 mem_pipeline_q == reset_ex_mem);
  assert property (disable iff (rst_i || ex_mem_flush_i) ex_mem_stall_i |-> ##1 $stable(
      mem_pipeline_q
  ));
  assert property (disable iff (rst_i || ex_mem_flush_i || ex_mem_stall_i) !ex_pipeline_d.valid |-> ##1 mem_pipeline_q == reset_ex_mem);

`endif
endmodule
