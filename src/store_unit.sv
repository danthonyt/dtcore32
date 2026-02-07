module store_unit (
  input  logic [31:0] mem_q_alu_csr_result,
  input  logic [31:0] mem_q_store_wdata,
  input  logic [2:0]  store_size_onehot,
  output logic [31:0] mem_wdata_o,
  output logic [3:0]  mem_wstrb,
  output logic        misaligned_store
);

  always @(*) begin
    misaligned_store = 0;
    mem_wdata_o      = 0;
    mem_wstrb        = 0;

    if (store_size_onehot[0]) begin // byte
      // never misaligned
      mem_wstrb   = 4'b1 << mem_q_alu_csr_result[1:0];
      mem_wdata_o = mem_q_store_wdata << (mem_q_alu_csr_result[1:0] * 8);
    end else if (store_size_onehot[1]) begin // half
      // misaligned when lsb = 1
      misaligned_store = mem_q_alu_csr_result[0];
      mem_wstrb        = 4'h3 << (mem_q_alu_csr_result[1] * 2);
      mem_wdata_o      = mem_q_store_wdata << (mem_q_alu_csr_result[1] * 16);
    end else if (store_size_onehot[2]) begin // word
      // misaligned when lsbs[1:0] != 2'b00
      misaligned_store = |mem_q_alu_csr_result[1:0];
      mem_wstrb        = 4'hf;
      mem_wdata_o      = mem_q_store_wdata;
    end else begin
      mem_wstrb        = 0;
      misaligned_store = 0;
    end
  end

endmodule
