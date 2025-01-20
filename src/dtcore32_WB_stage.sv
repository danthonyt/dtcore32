module dtcore32_WB_stage (
  /*
    input logic clk_i,
    input logic rst_i,
    // pipeline control
    input logic WB_stall_i,
    // pipeline in
    input logic MEM_reg_wr_en_i,
    input logic [1:0] MEM_result_src_i,
    input logic [31:0] DMEM_addr,
    input logic [31:0] MEM_dmem_rd_data_i,
    input logic [11:7] MEM_dest_reg_i,
    input logic [31:0] MEM_pc_plus_4_i,
    // pipeline out
    output logic WB_reg_wr_en_o,
    output logic [11:7] WB_dest_reg_o,
    //
    output logic [31:0] WB_result_o

  );

  logic [31:0] WB_alu_result;
  // pipeline out internal signals
  logic [1:0] WB_result_src;
  logic [31:0] WB_dmem_rd_data;
  logic [31:0] WB_pc_plus_4;

  // select data to write back to register file
  always_comb
  begin
    case (WB_result_src)
      2'b00:
        WB_result_o = WB_alu_result;
      2'b01:
        WB_result_o = WB_dmem_rd_data;
      2'b10:
        WB_result_o = WB_pc_plus_4;
      default:
        WB_result_o = 0;
    endcase
  end

  // pipeline to WB stage
  always_ff@(posedge clk_i)
  begin
    if(rst_i)
    begin
      WB_reg_wr_en_o <= 0;
      WB_result_src <= 0;
      WB_alu_result <= 0;
      WB_dmem_rd_data <= 0;
      WB_dest_reg_o <= 0;
      WB_pc_plus_4 <= 0;
    end
    else if(!WB_stall_i)
    begin
      WB_reg_wr_en_o <= MEM_reg_wr_en_i;
      WB_result_src <= MEM_result_src_i;
      WB_alu_result <= DMEM_addr;
      WB_dmem_rd_data <= MEM_dmem_rd_data_i;
      WB_dest_reg_o <= MEM_dest_reg_i;
      WB_pc_plus_4 <= MEM_pc_plus_4_i;
    end
  end
    */
    input logic clk_i,
    input logic rst_i,
    // pipeline control
    input logic WB_stall_i,
    // pipeline in
    input logic MEM_reg_wr_en_i,
    input logic [11:7] MEM_dest_reg_i,
    input logic [31:0] MEM_result_i,
    // pipeline out
    output logic WB_reg_wr_en_o,
    output logic [11:7] WB_dest_reg_o,
    //
    output logic [31:0] WB_result_o

  );


  // pipeline to WB stage
  always_ff@(posedge clk_i)
  begin
    if(rst_i)
    begin
      WB_reg_wr_en_o <= 0;
      WB_dest_reg_o <= 0;
      WB_result_o <= 0;
    end
    else if(!WB_stall_i)
    begin
      WB_reg_wr_en_o <= MEM_reg_wr_en_i;
      WB_dest_reg_o <= MEM_dest_reg_i;
      WB_result_o <= MEM_result_i;
    end
  end
endmodule

