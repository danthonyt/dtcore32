module dtcore32_WB_stage (
    input logic clk_i,
    input logic rst_i,
    // pipeline control
    input logic WB_stall_i,
    // pipeline in
    input logic MEM_reg_wr_en_i,
    input logic [11:7] MEM_dest_reg_i,
    input logic [31:0] MEM_result_i,
    input logic MEM_is_ecall_i,
    // pipeline out
    output logic WB_reg_wr_en_o,
    output logic [11:7] WB_dest_reg_o,
    //
    output logic [31:0] WB_result_o,
    output logic is_cpu_halted_o

  );
  logic WB_is_ecall;
  

  // pipeline to WB stage
  always_ff@(posedge clk_i)
  begin
    if(rst_i)
    begin
      WB_reg_wr_en_o <= 0;
      WB_dest_reg_o <= 0;
      WB_result_o <= 0;
      WB_is_ecall <= 0;
    end
    else if(!WB_stall_i)
    begin
      WB_reg_wr_en_o <= MEM_reg_wr_en_i;
      WB_dest_reg_o <= MEM_dest_reg_i;
      WB_result_o <= MEM_result_i;
      WB_is_ecall <= MEM_is_ecall_i;
    end
  end

  assign is_cpu_halted_o = WB_is_ecall;
endmodule

