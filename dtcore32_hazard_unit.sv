module dtcore32_hazard_unit(
    //Forwarding
    input logic clk_i,
    input logic rst_i,
    input logic [4:0] EX_rs1_addr_i,
    input logic [4:0] EX_rs2_addr_i,
    input logic [4:0] MEM_rd_addr_i,
    input logic [4:0] WB_rd_addr_i,
    input logic MEM_reg_wr_en_i,
    input logic WB_reg_wr_en_i,
    //Stalling
    input logic EX_result_src_b0_i,
    input logic [4:0] ID_rs1_addr_i,
    input logic [4:0] ID_rs2_addr_i,
    input logic [4:0] EX_rd_addr_i,
    input logic EX_dmem_rd_en_i,
    //branch control hazard
    input logic EX_pc_src_i,
    output logic [1:0] EX_forward_a_o,
    output logic [1:0] EX_forward_b_o,
    output logic ID_forward_a_o,
    output logic ID_forward_b_o,

    output logic ID_flush_o,
    output logic EX_flush_o,
    output logic MEM_flush_o,
    output logic WB_flush_o,

    output logic IF_stall_o,
    output logic ID_stall_o,
    output logic EX_stall_o,
    output logic MEM_stall_o,

    // trap logic
    input logic ID_trap_valid_i,
    input logic EX_trap_valid_i,
    input logic MEM_trap_valid_i,
    input logic WB_trap_valid_i

  );

  logic [1:0] EX_forward_a;
  logic [1:0] EX_forward_b;
  logic ID_forward_a;
  logic ID_forward_b;
  logic load_use_stall;
  logic DMEM_read_stall;
  always_ff @(posedge clk_i)
  begin
    if (rst_i) DMEM_read_stall <= 0;
    else
    begin
      if (DMEM_read_stall) DMEM_read_stall <= 0; // if stalled last cycle stop stalling
      else if (EX_dmem_rd_en_i) DMEM_read_stall <= 1;
    end
  end
  //if either source register matches a register we are writing to in a previous
  //instruction we must forward that value from the previous instruction so the updated
  //value is used.
  always_comb
  begin
    if ( ( (EX_rs1_addr_i == MEM_rd_addr_i) && MEM_reg_wr_en_i ) && (EX_rs1_addr_i != 0) )
      EX_forward_a =  2'b10;		//Forward from memory stage
    else if ( ( (EX_rs1_addr_i == WB_rd_addr_i) && WB_reg_wr_en_i ) && (EX_rs1_addr_i != 0) )
      EX_forward_a = 2'b01;	//Forward from Writeback stage
    else
      EX_forward_a = 2'b00;														//No Forwarding

    if ( ( (EX_rs2_addr_i == MEM_rd_addr_i) && MEM_reg_wr_en_i ) && (EX_rs2_addr_i != 0) )
      EX_forward_b =  2'b10;
    else if ( ( (EX_rs2_addr_i == WB_rd_addr_i) && WB_reg_wr_en_i ) && (EX_rs2_addr_i != 0))
      EX_forward_b = 2'b01;
    else
      EX_forward_b = 2'b00;
  end

  always_comb
  begin
    //We must stall if a load instruction is in the execute stage while another instruction has a matching source register to that write register in the decode stage
    if ((EX_result_src_b0_i && ((ID_rs1_addr_i == EX_rd_addr_i) || (ID_rs2_addr_i == EX_rd_addr_i))) )
      load_use_stall = 1;
    else
      load_use_stall = 0;
  end
  assign EX_forward_a_o = EX_forward_a;
  assign EX_forward_b_o = EX_forward_b;
  always_comb begin
    ID_forward_a = 0;
    ID_forward_b = 0;
    if ((ID_rs1_addr_i == WB_rd_addr_i) && (WB_reg_wr_en_i == 1))  ID_forward_a = 1;
    if ((ID_rs2_addr_i == WB_rd_addr_i) && (WB_reg_wr_en_i == 1))  ID_forward_b = 1;
  end


  assign ID_forward_a_o = ID_forward_a;
  assign ID_forward_b_o = ID_forward_b;
  assign ID_flush_o = (EX_pc_src_i | (ID_trap_valid_i & ~ID_stall_o) | (EX_trap_valid_i | MEM_trap_valid_i | WB_trap_valid_i)) & ~DMEM_read_stall;
  assign EX_flush_o = (((EX_pc_src_i | EX_trap_valid_i) & ~EX_stall_o)  | MEM_trap_valid_i | WB_trap_valid_i) & ~DMEM_read_stall;
  assign MEM_flush_o = (MEM_trap_valid_i & ~DMEM_read_stall)| WB_trap_valid_i ;
  assign WB_flush_o = WB_trap_valid_i;

  assign IF_stall_o = (load_use_stall & ~EX_pc_src_i) | DMEM_read_stall;
  assign ID_stall_o = (load_use_stall & ~EX_pc_src_i) | DMEM_read_stall;
  assign EX_stall_o = DMEM_read_stall;
  assign MEM_stall_o = DMEM_read_stall;

endmodule

