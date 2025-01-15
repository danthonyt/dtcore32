  
  `include "macros.svh"
  module dtcore32_IF_ID_reg
  (
    input logic clk_i,
    input logic rst_i,
    input logic ID_flush_i,
    input logic ID_stall_n_i,
    input logic [31:0] IMEM_rd_data_i,
    input logic [31:0] IMEM_addr_i,
    input logic [31:0] IF_pc_plus_4_i,
    output logic [31:0] ID_instr_o,
    output logic [31:0] ID_pc_o,
    output logic [31:0] ID_pc_plus_4_o
  );
 // IF/ID register
  always_ff @(posedge clk_i)
  begin
    if (rst_i || ID_flush_i)
    begin
      ID_instr_o <= `NOP_INSTRUCTION;
      ID_pc_o <= 0;
      ID_pc_plus_4_o <= 0 ;
    end
    else if (!ID_stall_n_i)
    begin
      ID_instr_o <= IMEM_rd_data_i;
      ID_pc_o <= IMEM_addr_i;
      ID_pc_plus_4_o <= IF_pc_plus_4_i;
    end
end
endmodule
