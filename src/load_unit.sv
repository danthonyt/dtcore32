module load_unit (
  input  logic [31:0] mem_rdata_i,
  input  logic [31:0] mem_q_alu_csr_result,
  input  logic [4:0]  load_size_onehot,
  output logic [3:0]  mem_rstrb,
  output logic [31:0] mem_load_rdata,
  output logic        misaligned_load
);

  wire [31:0] loaded;
  assign loaded = mem_rdata_i >> (8 * mem_q_alu_csr_result[1:0]);

  always_comb begin
    misaligned_load = 0;
    mem_rstrb       = 0;
    mem_load_rdata  = 0;

    if (load_size_onehot[0]) begin  // byte
      mem_rstrb      = 4'h1 << mem_q_alu_csr_result[1:0];
      mem_load_rdata = {{24{loaded[7]}}, loaded[7:0]};
    end else if (load_size_onehot[1]) begin  // byte unsigned
      mem_rstrb      = 4'h1 << mem_q_alu_csr_result[1:0];
      mem_load_rdata = {{24{1'b0}}, loaded[7:0]};
    end else if (load_size_onehot[2]) begin  // half
      misaligned_load = mem_q_alu_csr_result[0];
      mem_rstrb       = 4'h3 << (mem_q_alu_csr_result[1] * 2);
      mem_load_rdata  = {{16{loaded[15]}}, loaded[15:0]};
    end else if (load_size_onehot[3]) begin  // half unsigned
      misaligned_load = mem_q_alu_csr_result[0];
      mem_rstrb       = 4'h3 << (mem_q_alu_csr_result[1] * 2);
      mem_load_rdata  = {{16{1'b0}}, loaded[15:0]};
    end else if (load_size_onehot[4]) begin  // word
      misaligned_load = |mem_q_alu_csr_result[1:0];
      mem_rstrb       = 4'hf;
      mem_load_rdata  = loaded;
    end else begin
      mem_rstrb       = 0;
      misaligned_load = 0;
    end
  end

endmodule
