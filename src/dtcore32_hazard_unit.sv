module dtcore32_hazard_unit(
    //Forwarding
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
    //branch control hazard
    input logic EX_pc_src_i,
    output logic [1:0] EX_forward_a_o,
    output logic [1:0] EX_forward_b_o,
    output logic IF_stall_n_o,
    output logic ID_stall_n_o,
    output logic EX_flush_o,
    output logic ID_flush_o

  );

  logic [1:0] EX_forward_a;
  logic [1:0] EX_forward_b;
  logic IF_stall_n;
  logic ID_stall_n;
  logic EX_flush;
  logic ID_flush;

  //if either source register matches a register we are writing to in a previous
  //instruction we must forward that value from the previous instruction so the updated
  //value is used.
  always_comb
  begin
    if ( ( (EX_src_reg_1_i == MEM_dest_reg_i) & MEM_reg_wr_en_i ) & (EX_src_reg_1_i != 0) )
      EX_forward_a =  2'b10;		//Forward from memory stage
    else if ( ( (EX_src_reg_1_i == WB_dest_reg_i) & WB_reg_wr_en_i ) & (EX_src_reg_1_i != 0) )
      EX_forward_a = 2'b01;	//Forward from Writeback stage
    else
      EX_forward_a = 2'b00;														//No Forwarding

    if ( ( (EX_src_reg_2_i == MEM_dest_reg_i) & MEM_reg_wr_en_i ) & (EX_src_reg_2_i != 0) )
      EX_forward_b =  2'b10;
    else if ( ( (EX_src_reg_2_i == WB_dest_reg_i) & WB_reg_wr_en_i ) & (EX_src_reg_2_i != 0))
      EX_forward_b = 2'b01;
    else
      EX_forward_b = 2'b00;
  end

  always_comb
  begin
    //We must stall if a load instruction is in the execute stage while another instruction has a matching source register to that write register in the decode stage
    if ((EX_result_src_b0_i & ((ID_src_reg_1_i == EX_dest_reg_i) | (ID_src_reg_2_i == EX_dest_reg_i))) )
      {IF_stall_n, ID_stall_n} = 2'b1_1;
    else
      {IF_stall_n, ID_stall_n} = 2'b0_0;
  end

  assign ID_flush = EX_pc_src_i ;
  assign EX_flush = ID_stall_n | EX_pc_src_i;

  assign EX_forward_a_o = EX_forward_a;
  assign EX_forward_b_o = EX_forward_b;
  assign IF_stall_n_o = IF_stall_n;
  assign ID_stall_n_o = ID_stall_n;
  assign EX_flush_o = EX_flush;
  assign ID_flush_o = ID_flush;
endmodule

