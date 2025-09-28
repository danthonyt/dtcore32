//===========================================================
// Project    : RISC-V CPU / Digital Memory Modules
// File       : rom.v
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
    input  clk_i,
    input  [$clog2(MEM_DEPTH)-1+2:2] insn_addr_i,
    input  [$clog2(MEM_DEPTH)-1+2:2] mem_addr_i,
    input  mem_en_i,
    output reg [31:0] insn_rdata_o,
    output reg [31:0] mem_rdata_o

);
  reg [31:0] MEM[MEM_DEPTH-1:0];

  initial begin
    $readmemh("coremark_program.mem", MEM);
    //$readmemh("hello_world.mem", MEM);
  end

  always @(posedge clk_i) begin
    insn_rdata_o <= MEM[insn_addr_i];
    if (mem_en_i) begin
      mem_rdata_o <= MEM[mem_addr_i];
    end
  end
endmodule
