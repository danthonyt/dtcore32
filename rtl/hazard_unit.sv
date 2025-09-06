module hazard_unit
  import params_pkg::*;
(
    //Forwarding
    input logic [4:0] ex_rs1_addr_i,
    input logic [4:0] ex_rs2_addr_i,
    input logic [4:0] mem_rd_addr_i,
    input logic [4:0] wb_rd_addr_i,
    input logic [4:0] id_rs1_addr_i,
    input logic [4:0] id_rs2_addr_i,
    input logic [4:0] ex_rd_addr_i,
    input logic ex_is_pc_redirect_i,
    output logic [2:0] ex_forward_a_sel_o,
    output logic [2:0] ex_forward_b_sel_o,
    output logic id_forward_a_o,
    output logic id_forward_b_o,
    output logic if_id_flush_o,
    output logic id_ex_flush_o,
    output logic ex_mem_flush_o,
    output logic mem_wb_flush_o,
    output logic if_id_stall_o,
    output logic id_ex_stall_o,
    output logic ex_mem_stall_o,
    output logic mem_wb_stall_o,
    input logic ex_trap_valid_i,
    input logic mem_trap_valid_i,
    input logic wb_trap_valid_i,
    input logic mem_req_i,
    input logic mem_done_i,
    input mem_op_t ex_mem_op_i

);

  logic mem_req_stall;
  logic [2:0] ex_forward_a;
  logic [2:0] ex_forward_b;
  logic id_forward_a;
  logic id_forward_b;
  logic load_use_hazard;
  logic nonzero_id_rs1;
  logic nonzero_id_rs2;
  logic id_ex_rs1_match;
  logic id_ex_rs2_match;
  logic ex_mem_rs2_match;
  logic ex_mem_rs1_match;
  logic ex_wb_rs2_match;
  logic ex_wb_rs1_match;
  logic nonzero_ex_rs1;
  logic nonzero_ex_rs2;
  assign nonzero_id_rs1 = |id_rs1_addr_i;
  assign nonzero_id_rs2 = |id_rs2_addr_i;
  assign id_ex_rs1_match = (id_rs1_addr_i == ex_rd_addr_i);
  assign id_ex_rs2_match = (id_rs2_addr_i == ex_rd_addr_i);
  assign nonzero_ex_rs1 = ex_rs1_addr_i != 0;
  assign nonzero_ex_rs2 = ex_rs2_addr_i != 0;
  assign ex_mem_rs1_match = ((ex_rs1_addr_i == mem_rd_addr_i) && nonzero_ex_rs1);
  assign ex_mem_rs2_match = ((ex_rs2_addr_i == mem_rd_addr_i) && nonzero_ex_rs2);
  assign ex_wb_rs1_match = ((ex_rs1_addr_i == wb_rd_addr_i) && nonzero_ex_rs1);
  assign ex_wb_rs2_match = ((ex_rs2_addr_i == wb_rd_addr_i) && nonzero_ex_rs2);

  /*****************************************/
  //
  //  STALL LOGIC
  //
  /*****************************************/
  // stall if axil transaction is still not done

  // We must stall if a load instruction is in the execute stage while another instruction 
  // has a matching source register to that write register in the decode stage
  assign load_use_hazard = ((ex_mem_op_i[4] & ~ex_mem_op_i[3] ) && ((id_ex_rs1_match && nonzero_id_rs1)
   || (id_ex_rs2_match && nonzero_id_rs2))) ? 1 : 0;

  assign mem_req_stall = mem_req_i && !mem_done_i;

  /*****************************************/
  //
  //  FORWARDING LOGIC
  //
  /*****************************************/

  //if either source register matches a register we are writing to in a previous
  //instruction we must forward that value from the previous instruction so the updated
  //value is used.
  always_comb begin
    if (ex_mem_rs1_match) ex_forward_a = FORWARD_SEL_MEM_RESULT;
    else if (ex_wb_rs1_match) ex_forward_a = FORWARD_SEL_WB_RESULT;
    else ex_forward_a = NO_FORWARD_SEL;

    if (ex_mem_rs2_match) ex_forward_b = FORWARD_SEL_MEM_RESULT;
    else if (ex_wb_rs2_match) ex_forward_b = FORWARD_SEL_WB_RESULT;
    else ex_forward_b = NO_FORWARD_SEL;
  end

  assign ex_forward_a_sel_o = ex_forward_a;
  assign ex_forward_b_sel_o = ex_forward_b;
  assign id_forward_a = ((id_rs1_addr_i == wb_rd_addr_i));
  assign id_forward_b = ((id_rs2_addr_i == wb_rd_addr_i));


  // LOAD USE FLUSHES ID/EX AND STALLS IF/ID
  /*****************************************/
  //
  //  OUTPUT ASSIGNMENTS
  //
  /*****************************************/

  assign id_forward_a_o = id_forward_a;
  assign id_forward_b_o = id_forward_b;

  assign if_id_flush_o = ex_is_pc_redirect_i | (ex_trap_valid_i | mem_trap_valid_i | wb_trap_valid_i);
  assign id_ex_flush_o = (ex_is_pc_redirect_i & ~ex_mem_stall_o) | (mem_trap_valid_i | wb_trap_valid_i);
  assign ex_mem_flush_o = mem_trap_valid_i | wb_trap_valid_i;
  assign mem_wb_flush_o = wb_trap_valid_i;

  assign if_id_stall_o = load_use_hazard | id_ex_stall_o;
  assign id_ex_stall_o = ex_mem_stall_o;
  assign ex_mem_stall_o = mem_req_stall;
  assign mem_wb_stall_o = mem_req_stall;


endmodule
