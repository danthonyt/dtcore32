//===========================================================
// Project    : RISC-V CPU / Digital Memory Modules
// File       : ram.sv
// Module     : ram
// Description: Parameterizable synchronous RAM module. Supports 
//              byte-enable writes and single-clock read/write operations.
//
// Parameters:
//   MEM_DEPTH - Depth of the memory in 32-bit words (default: 256)
//
// Inputs:
//   clk_i     - System clock
//   addr_i    - Memory address input (word-aligned)
//   en_i      - Memory enable
//   wen_i     - Write enable
//   wdata_i   - Write data input
//   wstrb_i   - Byte-enable strobes for write operations
//
// Outputs:
//   rdata_o   - Data output
//
// Notes:
//   - Synchronous RAM with clocked read data.
//   - Supports byte-level write enable (wstrb_i).
//   - Address bus is word-aligned; calculated with $clog2(MEM_DEPTH).
//
// Author     : David Torres
// Date       : 2025-09-16
//===========================================================

module ram #(
    parameter MEM_DEPTH = 256
) (
    input logic clk_i,
    input logic [$clog2(MEM_DEPTH)-1+2:2] addr_i,
    input logic en_i,
    input logic wen_i,
    input logic [31:0] wdata_i,
    input logic [3:0] wstrb_i,
    output logic [31:0] rdata_o
);
  logic [31:0] MEM[MEM_DEPTH-1:0];

  initial begin
    $readmemh("cm_dmem.mem", MEM);
  end

  integer i;
  always @(posedge clk_i) begin
    if (en_i) begin
      if (wen_i) begin
        for (i = 0; i < 4; i = i + 1) begin
          if (wstrb_i[i]) MEM[addr_i][i*8+:8] <= wdata_i[i*8+:8];
        end
      end
      rdata_o <= MEM[addr_i];
    end
  end
endmodule
