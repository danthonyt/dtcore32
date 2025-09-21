//===========================================================
// Project    : RISC-V CPU
// File       : load_unit.sv
// Module     : load_unit
// Description: Load data formatting unit. Handles byte/halfword/word
//              loads from memory, generates proper byte-enable strobes,
//              checks for misaligned accesses, and outputs aligned data.
//
// Inputs:
//   mem_size_onehot      - One-hot encoding for memory access size (byte/halfword/word)
//   raddr_lower2_i       - Lower 2 bits of read address (for alignment)
//   rdata_unformatted_i  - Raw data read from memory
//
// Outputs:
//   misaligned_load_o    - High if load address is misaligned
//   rstrb_o              - Byte-enable strobe for memory access
//   rdata_o              - Formatted, aligned read data
//
// Notes:
//   - Supports all RISC-V load types (LB, LBU, LH, LHU, LW).
//   - Works combinationally to quickly format memory data for the pipeline.
//   - Misaligned loads can trigger exceptions or trap handling downstream.
//
// Author     : David Torres
// Date       : 2025-09-16
//===========================================================

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
      // never misaligned
      strb = 4'h1 << raddr_lower2_i;
      load_formatted = {{24{loaded[7]}}, loaded[7:0]};
    end else if (mem_size_onehot[1]) begin  // byte unsigned
      // never misaligned
      strb = 4'h1 << raddr_lower2_i;
      load_formatted = {{24{1'b0}}, loaded[7:0]};
    end else if (mem_size_onehot[2]) begin  // half
      // misaligned when lsb = 1
      misaligned_load = raddr_lower2_i[0];
      strb = 4'h3 << (raddr_lower2_i[1] * 2);
      load_formatted = {{16{loaded[15]}}, loaded[15:0]};
    end else if (mem_size_onehot[3]) begin  // half unsigned
      // misaligned when lsb = 1
      misaligned_load = raddr_lower2_i[0];
      strb = 4'h3 << (raddr_lower2_i[1] * 2);
      load_formatted = {{16{1'b0}}, loaded[15:0]};
    end else if (mem_size_onehot[4]) begin  // word
       // misaligned when at least one of the lower 2 bits are nonzero
      misaligned_load = |raddr_lower2_i;
      strb = 4'hf;
      load_formatted = loaded;
    end else begin
      strb = 0;
      misaligned_load = 0;
    end
  end
  assign rstrb_o            = strb;
  assign misaligned_load_o  = misaligned_load;
  assign rdata_o            = load_formatted;
endmodule
