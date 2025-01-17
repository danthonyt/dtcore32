`include "macros.svh"
module dtcore32_IF_stage (
    input logic clk_i,
    input logic rst_i,
    input logic IF_stall_i,
    input logic [31:0] EX_pc_target_i,
    input logic EX_pc_src_i,
    output logic [31:0] IMEM_addr_o,
    output logic [31:0] IF_pc_plus_4_o

  );

  logic [31:0] IF_pc_tick;

  always_ff @(posedge clk_i)
  begin
    if (rst_i)
      IMEM_addr_o <= 0;
    else if (!IF_stall_i)
      IMEM_addr_o <= IF_pc_tick;
  end

  // next pc logic
  always_comb begin
    unique case (EX_pc_src_i)
      // select pc incremented by 4 
      1'b0: begin
        IF_pc_tick = IF_pc_plus_4_o;
      end
      // select pc from execute stage
      1'b1:begin
        IF_pc_tick = EX_pc_target_i;
      end
    endcase
  end
  
  // pc incremented by 4
  assign IF_pc_plus_4_o = IMEM_addr_o + 4;

  
endmodule


