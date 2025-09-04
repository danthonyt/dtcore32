module hazard_unit
  import params_pkg::*;
(
    //Forwarding
    input logic [4:0] ex_rs1_addr_i,
    input logic [4:0] ex_rs2_addr_i,
    input logic [4:0] mem_rd_addr_i,
    input logic [4:0] wb_rd_addr_i,
    input result_sel_t ex_result_sel_i,
    input result_sel_t wb_result_sel_i,
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
    input logic mem_done_i

);

  logic wishbone_stall;
  logic [2:0] ex_forward_a;
  logic [2:0] ex_forward_b;
  logic if_forward_a;
  logic id_forward_b;
  logic load_use_hazard;
  logic nonzero_ID_rs1;
  logic nonzero_ID_rs2;
  logic id_ex_rs1_match;
  logic id_ex_rs2_match;
  logic ex_mem_rs2_match;
  logic ex_mem_rs1_match;
  logic ex_wb_rs2_match;
  logic ex_wb_rs1_match;
  assign nonzero_ID_rs1 = |id_rs1_addr_i;
  assign nonzero_ID_rs2 = |id_rs2_addr_i;
  assign id_ex_rs1_match = (id_rs1_addr_i == ex_rd_addr_i);
  assign id_ex_rs2_match = (id_rs2_addr_i == ex_rd_addr_i);
  assign ex_mem_rs1_match = ((ex_rs1_addr_i == mem_rd_addr_i) && (ex_rs1_addr_i != 0));
  assign ex_mem_rs2_match = ((ex_rs2_addr_i == mem_rd_addr_i) && (ex_rs2_addr_i != 0));
  assign ex_wb_rs1_match = ((ex_rs1_addr_i == wb_rd_addr_i) && (ex_rs1_addr_i != 0));
  assign ex_wb_rs2_match = ((ex_rs2_addr_i == wb_rd_addr_i) && (ex_rs2_addr_i != 0));

  /*****************************************/
  //
  //  STALL LOGIC
  //
  /*****************************************/
  // stall if axil transaction is still not done

  // We must stall if a load instruction is in the execute stage while another instruction 
  // has a matching source register to that write register in the decode stage
  assign load_use_hazard = ((ex_result_sel_i == RESULT_SEL_MEM_DATA) && ((id_ex_rs1_match && nonzero_ID_rs1)
   || (id_ex_rs2_match && nonzero_ID_rs2))) ? 1 : 0;

  assign wishbone_stall = mem_req_i && !mem_done_i;

  /*****************************************/
  //
  //  FORWARDING LOGIC
  //
  /*****************************************/

  //if either source register matches a register we are writing to in a previous
  //instruction we must forward that value from the previous instruction so the updated
  //value is used.
  always_comb begin
    if (ex_mem_rs1_match) ex_forward_a = FORWARD_SEL_MEM_ALU_RESULT;
    else if (ex_wb_rs1_match && (wb_result_sel_i == RESULT_SEL_MEM_DATA))
      ex_forward_a = FORWARD_SEL_WB_LOAD_RDATA;
    else if (ex_wb_rs1_match) ex_forward_a = FORWARD_SEL_WB_ALU_RESULT;
    else ex_forward_a = NO_FORWARD_SEL;

    if (ex_mem_rs2_match) ex_forward_b = FORWARD_SEL_MEM_ALU_RESULT;
    else if (ex_wb_rs2_match && (wb_result_sel_i == RESULT_SEL_MEM_DATA))
      ex_forward_b = FORWARD_SEL_WB_LOAD_RDATA;
    else if (ex_wb_rs2_match) ex_forward_b = FORWARD_SEL_WB_ALU_RESULT;
    else ex_forward_b = NO_FORWARD_SEL;
  end

  assign ex_forward_a_sel_o = ex_forward_a;
  assign ex_forward_b_sel_o = ex_forward_b;
  assign if_forward_a = (id_rs1_addr_i == wb_rd_addr_i);
  assign id_forward_b = (id_rs2_addr_i == wb_rd_addr_i);


  // LOAD USE FLUSHES ID/EX AND STALLS IF/ID
  /*****************************************/
  //
  //  OUTPUT ASSIGNMENTS
  //
  /*****************************************/

  assign id_forward_a_o = if_forward_a;
  assign id_forward_b_o = id_forward_b;

  assign if_id_flush_o = ex_is_pc_redirect_i | (ex_trap_valid_i | mem_trap_valid_i | wb_trap_valid_i);
  assign id_ex_flush_o = (ex_is_pc_redirect_i & ~ex_mem_stall_o) | (mem_trap_valid_i | wb_trap_valid_i);
  assign ex_mem_flush_o = mem_trap_valid_i | wb_trap_valid_i;
  assign mem_wb_flush_o = wb_trap_valid_i;

  assign if_id_stall_o = load_use_hazard | id_ex_stall_o;
  assign id_ex_stall_o = ex_mem_stall_o;
  assign ex_mem_stall_o = wishbone_stall;
  assign mem_wb_stall_o = wishbone_stall;


endmodule
