module dtcore32_hazard_unit(
    //Forwarding
    input logic clk_i,
    input logic rst_i,
    input logic [4:0] EX_src_reg_1_i,
    input logic [4:0] EX_src_reg_2_i,
    input logic [4:0] MEM_dest_reg_i,
    input logic [4:0] WB_dest_reg_i,
    input logic MEM_reg_wr_en_i,
    input logic WB_reg_wr_en_i,
    //Stalling
    input logic EX_result_src_b0_i,
    input logic [4:0] ID_src_reg_1_i,
    input logic [4:0] ID_src_reg_2_i,
    input logic [4:0] EX_dest_reg_i,
    input logic EX_dmem_read_i,
    //branch control hazard
    input logic EX_pc_src_i,
    output logic [1:0] EX_forward_a_o,
    output logic [1:0] EX_forward_b_o,

    output logic ID_flush_o,
    output logic EX_flush_o,
    output logic MEM_flush_o,

    output logic IF_stall_o,
    output logic ID_stall_o,
    output logic EX_stall_o,
    output logic MEM_stall_o,
    output logic WB_stall_o,

    // trap logic
    input logic EX_trap_valid_i,
    input logic MEM_trap_valid_i,
    input logic WB_trap_valid_i

  );

  logic [1:0] EX_forward_a;
  logic [1:0] EX_forward_b;
  logic IF_load_use_stall;
  logic ID_load_use_stall;
  logic DMEM_read_stall;
  always_ff @(posedge clk_i)
  begin
    if (rst_i) DMEM_read_stall <= 0;
    else
    begin
      if (DMEM_read_stall) DMEM_read_stall <= 0; // if stalled last cycle stop stalling
      else if (EX_dmem_read_i) DMEM_read_stall <= 1;
    end
  end
  //if either source register matches a register we are writing to in a previous
  //instruction we must forward that value from the previous instruction so the updated
  //value is used.
  always_comb
  begin
    if ( ( (EX_src_reg_1_i == MEM_dest_reg_i) && MEM_reg_wr_en_i ) && (EX_src_reg_1_i != 0) )
      EX_forward_a =  2'b10;		//Forward from memory stage
    else if ( ( (EX_src_reg_1_i == WB_dest_reg_i) && WB_reg_wr_en_i ) && (EX_src_reg_1_i != 0) )
      EX_forward_a = 2'b01;	//Forward from Writeback stage
    else
      EX_forward_a = 2'b00;														//No Forwarding

    if ( ( (EX_src_reg_2_i == MEM_dest_reg_i) && MEM_reg_wr_en_i ) && (EX_src_reg_2_i != 0) )
      EX_forward_b =  2'b10;
    else if ( ( (EX_src_reg_2_i == WB_dest_reg_i) && WB_reg_wr_en_i ) && (EX_src_reg_2_i != 0))
      EX_forward_b = 2'b01;
    else
      EX_forward_b = 2'b00;
  end

  always_comb
  begin
    //We must stall if a load instruction is in the execute stage while another instruction has a matching source register to that write register in the decode stage
    if ((EX_result_src_b0_i && ((ID_src_reg_1_i == EX_dest_reg_i) || (ID_src_reg_2_i == EX_dest_reg_i))) )
      {IF_load_use_stall, ID_load_use_stall} = 2'b1_1;
    else
      {IF_load_use_stall, ID_load_use_stall} = 2'b0_0;
  end
  assign EX_forward_a_o = EX_forward_a;
  assign EX_forward_b_o = EX_forward_b;

  assign ID_flush_o = EX_pc_src_i | EX_trap_valid_i | MEM_trap_valid_i | WB_trap_valid_i;
  assign EX_flush_o = EX_pc_src_i | MEM_trap_valid_i | WB_trap_valid_i;
  assign MEM_flush_o = WB_trap_valid_i;

  assign IF_stall_o = IF_load_use_stall | DMEM_read_stall;
  assign ID_stall_o = ID_load_use_stall | DMEM_read_stall;
  assign EX_stall_o = DMEM_read_stall;
  assign MEM_stall_o = DMEM_read_stall;
  assign WB_stall_o = DMEM_read_stall;

endmodule

