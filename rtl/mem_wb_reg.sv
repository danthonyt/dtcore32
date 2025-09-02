module mem_wb_reg
  import params_pkg::*;
(
    input logic clk_i,
    input logic rst_i,
    input logic mem_wb_stall_i,
    input logic mem_wb_flush_i,
    input mem_wb_t mem_pipeline_d,
    output mem_wb_t wb_pipeline_q
);
  mem_wb_t reset_mem_wb;
  always_comb begin
    reset_mem_wb              = '0;  // zero all simple/packed fields
    reset_mem_wb.carried_trap = '0;  // zero the nested trap struct
    reset_mem_wb.insn         = 32'h00000013;  // NOP
  end
  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      wb_pipeline_q <= reset_mem_wb;
    end else if (mem_wb_flush_i) begin
      wb_pipeline_q <= reset_mem_wb;
    end else if (!mem_wb_stall_i) begin
      if (!mem_pipeline_d.valid) begin
        wb_pipeline_q <= reset_mem_wb;
      end else begin
        wb_pipeline_q <= mem_pipeline_d;
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
  assert property (rst_i || mem_wb_flush_i |-> ##1 wb_pipeline_q == reset_mem_wb);
  assert property (disable iff (rst_i || mem_wb_flush_i) mem_wb_stall_i |-> ##1 $stable(
      wb_pipeline_q
  ));
  assert property (disable iff (rst_i || mem_wb_flush_i || mem_wb_stall_i) !mem_pipeline_d.valid |-> ##1 wb_pipeline_q == reset_mem_wb);

`endif
endmodule
