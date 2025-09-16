//===========================================================
// Project    : RISC-V CPU / Digital Memory Modules
// File       : rom.sv
// Module     : rom
// Description: Parameterizable synchronous ROM module. Provides
//              read-only memory with single-clock access. Can be
//              used for instruction storage or constant data.
//
// Parameters:
//   MEM_DEPTH - Depth of the memory in 32-bit words (default: 256)
//
// Inputs:
//   clk_i     - System clock
//   addr_i    - Memory address input (word-aligned)
//
// Outputs:
//   rdata_o   - Data output
//
// Notes:
//   - Synchronous read; data is available after rising clock edge.
//   - Address bus is word-aligned; calculated with $clog2(MEM_DEPTH).
//
// Author     : David Torres
// Date       : 2025-09-16
//===========================================================

module rom #(
    parameter MEM_DEPTH = 256
) (
    input logic clk_i,
    input logic [$clog2(MEM_DEPTH)-1+2:2] addr_i,
    output logic [31:0] rdata_o
);
  logic [31:0] MEM[MEM_DEPTH-1:0];

  initial begin
    $readmemh("imem.mem", MEM);
  end

  always @(posedge clk_i) begin
    rdata_o <= MEM[addr_i];
  end
endmodule
