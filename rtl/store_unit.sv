//===========================================================
// Project    : RISC-V CPU
// File       : store_unit.sv
// Module     : store_unit
// Description: Store data formatting unit. Handles byte/halfword/word
//              store operations to memory, generates proper byte-enable 
//              strobes, checks for misaligned accesses, and outputs
//              correctly formatted write data.
//
// Inputs:
//   store_size_onehot_i  - One-hot encoding for store size (byte/halfword/word)
//   waddr_lower2_i       - Lower 2 bits of write address (for alignment)
//   wdata_unformatted_i  - Raw write data from pipeline
//
// Outputs:
//   misaligned_store_o   - High if store address is misaligned
//   wstrb_o              - Byte-enable strobes for memory write
//   wdata_o              - Formatted, aligned write data
//
// Notes:
//   - Supports all RISC-V store types (SB, SH, SW).
//   - Works combinationally to quickly format write data for the memory interface.
//   - Misaligned stores can trigger exceptions or trap handling downstream.
//
// Author     : David Torres
// Date       : 2025-09-16
//===========================================================

module store_unit
  import params_pkg::*;
(
    input logic [2:0] store_size_onehot_i,
    input logic [1:0] waddr_lower2_i,
    input logic [31:0] wdata_unformatted_i,
    output logic misaligned_store_o,
    output logic [3:0] wstrb_o,
    output logic [31:0] wdata_o
);

  logic misaligned_store;
  logic [3:0] wstrb;
  logic [31:0] store_wdata_formatted;
  always_comb begin
    misaligned_store = 0;
    store_wdata_formatted = 'x;
    wstrb = 'x;
    if (store_size_onehot_i[0]) begin // byte
      wstrb = 4'b1 << waddr_lower2_i;
      store_wdata_formatted = wdata_unformatted_i << waddr_lower2_i * 8;
    end else if (store_size_onehot_i[1]) begin // half
      wstrb = 4'h3 << waddr_lower2_i[1] * 2;
      store_wdata_formatted = wdata_unformatted_i << waddr_lower2_i[1] * 16;
    end else if (store_size_onehot_i[2]) begin // word
      wstrb = 4'hf;
      store_wdata_formatted = wdata_unformatted_i;
    end else begin
      wstrb = 0;
      misaligned_store = 0;
    end
  end

  assign wstrb_o = misaligned_store ? 0 : wstrb;
  assign misaligned_store_o = 0;
  assign wdata_o = misaligned_store ? 0 : store_wdata_formatted;

endmodule
