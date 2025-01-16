`include "macros.svh"
module dtcore32_IF_stage (
    input logic clk_i,
    input logic rst_i,
    input logic IF_stall_i,
    input logic [31:0] EX_pc_target_i,
    input logic EX_pc_src_i,
    output logic [31:0] IF_pc_plus_4_o,
    output logic [31:0] IMEM_addr_o,

    input logic ID_flush_i,
    input logic ID_stall_i,
    input logic [31:0] IMEM_rd_data_i,
    input logic [31:0] IMEM_addr_i,
    output logic [31:0] ID_instr_o,
    output logic [31:0] ID_pc_o,
    output logic [31:0] ID_pc_plus_4_o


  );
  logic [31:0] ID_instr;
  logic [31:0] ID_pc;
  logic [31:0] ID_pc_plus_4;

  logic [31:0] IF_pc_plus_4;
  logic [31:0] IMEM_addr;

  logic [31:0] IF_pc_tick;
  always_ff @(posedge clk_i)
  begin
    if (rst_i)
      IMEM_addr <= 0;
    else if (!IF_stall_i)
      IMEM_addr <= IF_pc_tick;
  end

  mux2to1 # (
            .WIDTH(32)
          )
          mux2to1_inst (
            .in0(IF_pc_plus_4),
            .in1(EX_pc_target_i),
            .sel(EX_pc_src_i),
            .out(IF_pc_tick)
          );

  adder # (
          .WIDTH(32)
        )
        adder_inst (
          .in1(IMEM_addr),
          .in2(32'd4),
          .sum(IF_pc_plus_4)
        );
  assign IF_pc_plus_4_o = IF_pc_plus_4;
  assign IMEM_addr_o = IMEM_addr;

  // IF/ID register
  always_ff @(posedge clk_i)
  begin
    if (rst_i || ID_flush_i)
    begin
      ID_instr <= `NOP_INSTRUCTION;
      ID_pc <= 0;
      ID_pc_plus_4 <= 0 ;
    end
    else if (!ID_stall_i)
    begin
      ID_instr <= IMEM_rd_data_i;
      ID_pc <= IMEM_addr_i;
      ID_pc_plus_4 <= IF_pc_plus_4;
    end
  end

  assign ID_instr_o = ID_instr;
  assign ID_pc_o =  ID_pc;
  assign ID_pc_plus_4_o = ID_pc_plus_4;
endmodule


