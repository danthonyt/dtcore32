module dtcore32_WB_stage (
    input logic [1:0] WB_result_src_i,
    input logic [31:0] WB_alu_result_i,
    input logic [31:0] WB_dmem_rd_data_i,
    input logic [31:0] WB_pc_plus_4_i,
    input logic [31:0] WB_csr_rd_data_i,
    output logic [31:0] WB_result_o

  );
  logic [31:0] WB_result;
  mux4to1 # (
            .WIDTH(32)
          )
          mux4to1_inst (
            .in0(WB_alu_result_i),
            .in1(WB_dmem_rd_data_i),
            .in2(WB_pc_plus_4_i),
            .in3(WB_csr_rd_data_i),
            .sel(WB_result_src_i),
            .out(WB_result)
          );
  assign WB_result_o = WB_result;
endmodule

