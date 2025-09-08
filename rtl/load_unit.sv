module load_unit
  import params_pkg::*;
(
    // 
    input logic [4:0] mem_size_onehot,
    input logic [1:0] raddr_lower2_i,
    input logic [31:0] rdata_unformatted_i,
    output logic misaligned_load_o,
    output logic [3:0] rstrb_o,
    output logic [31:0] rdata_o
);
  logic [31:0] loaded;
  logic misaligned_load;
  logic [3:0] strb;
  logic [31:0] load_formatted;
  assign loaded = rdata_unformatted_i >> 8 * (raddr_lower2_i);
  // logic to determine which bits of the read data from data memory will be loaded for load instructions
  always_comb begin
    misaligned_load = 0;
    strb = 'x;
    load_formatted = 'x;
    if (mem_size_onehot[0]) begin  // byte
      strb = 4'h1;
      load_formatted = {{24{loaded[7]}}, loaded[7:0]};
    end else if (mem_size_onehot[1]) begin  // byte unsigned
      strb = 4'h1;
      load_formatted = {{24{1'b0}}, loaded[7:0]};
    end else if (mem_size_onehot[2]) begin  // half
      strb = 4'h3;
      load_formatted = {{16{loaded[15]}}, loaded[15:0]};
    end else if (mem_size_onehot[3]) begin  // half unsigned
      strb = 4'h3;
      load_formatted = {{16{1'b0}}, loaded[15:0]};
    end else if (mem_size_onehot[4]) begin  // word
      strb = 4'hf;
      load_formatted = loaded;
    end else begin
      strb = 0;
      misaligned_load = 0;
    end
  end
  assign rstrb_o            = misaligned_load ? 0 : strb;
  assign misaligned_load_o  = misaligned_load;
  assign rdata_o            = load_formatted;
endmodule
