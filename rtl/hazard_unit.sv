module hazard_unit
  import params_pkg::*;
(
    // forward condition signals
    input logic mem_is_rd_write_i,
    input logic wb_is_rd_write_i,
    // register addresses
    input logic [4:0] id_rs1_addr_i,
    input logic [4:0] id_rs2_addr_i,
    input logic [4:0] ex_rs1_addr_i,
    input logic [4:0] ex_rs2_addr_i,
    input logic [4:0] ex_rd_addr_i,
    input logic [4:0] mem_rd_addr_i,
    input logic [4:0] wb_rd_addr_i,
    // forward select signals
    output logic id_forward_a_o,
    output logic id_forward_b_o,
    output logic [2:0] ex_forward_a_sel_o,
    output logic [2:0] ex_forward_b_sel_o,
    // flush and stall condition signals
    input logic mem_jump_taken_i,
    // mem signals
    input logic mem_req_i,
    input logic mem_done_i,
    input logic ex_is_mem_read_i,
    // flush signals
    output logic if_id_flush_o,
    output logic id_ex_flush_o,
    output logic ex_mem_flush_o,
    output logic mem_wb_flush_o,
    // stall signals
    output logic if_id_stall_o,
    output logic id_ex_stall_o,
    output logic ex_mem_stall_o,
    output logic mem_wb_stall_o,
    // valid trap signals
    input logic ex_trap_valid_i,
    input logic mem_trap_valid_i,
    input logic wb_trap_valid_i
);

  logic mem_req_stall;
  logic [2:0] ex_forward_a;
  logic [2:0] ex_forward_b;
  logic id_forward_a;
  logic id_forward_b;
  logic load_use_hazard;
  logic id_wb_rs1_match;
  logic id_wb_rs2_match;
  logic id_ex_rs1_match;
  logic id_ex_rs2_match;
  logic ex_mem_rs2_match;
  logic ex_mem_rs1_match;
  logic ex_wb_rs2_match;
  logic ex_wb_rs1_match;
  assign id_wb_rs1_match = (id_rs1_addr_i == wb_rd_addr_i) && |id_rs1_addr_i;
  assign id_wb_rs2_match = (id_rs2_addr_i == wb_rd_addr_i) && |id_rs2_addr_i;
  assign id_ex_rs1_match = (id_rs1_addr_i == ex_rd_addr_i) && |id_rs1_addr_i;
  assign id_ex_rs2_match = (id_rs2_addr_i == ex_rd_addr_i) && |id_rs2_addr_i;
  assign ex_mem_rs1_match = ((ex_rs1_addr_i == mem_rd_addr_i) && |ex_rs1_addr_i);
  assign ex_mem_rs2_match = ((ex_rs2_addr_i == mem_rd_addr_i) && |ex_rs2_addr_i);
  assign ex_wb_rs1_match = ((ex_rs1_addr_i == wb_rd_addr_i) && |ex_rs1_addr_i);
  assign ex_wb_rs2_match = ((ex_rs2_addr_i == wb_rd_addr_i) && |ex_rs2_addr_i);

  /*****************************************/
  //
  //  STALL LOGIC
  //
  /*****************************************/
  // stall if axil transaction is still not done

  // We must stall if a load instruction is in the execute stage while another instruction 
  // has a matching source register to that write register in the decode stage
  assign load_use_hazard = (ex_is_mem_read_i && (id_ex_rs1_match || id_ex_rs2_match));

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
    if (ex_mem_rs1_match && mem_is_rd_write_i) ex_forward_a = FORWARD_SEL_MEM_RESULT;
    else if (ex_wb_rs1_match && wb_is_rd_write_i) ex_forward_a = FORWARD_SEL_WB_RESULT;
    else ex_forward_a = NO_FORWARD_SEL;

    if (ex_mem_rs2_match && mem_is_rd_write_i) ex_forward_b = FORWARD_SEL_MEM_RESULT;
    else if (ex_wb_rs2_match && wb_is_rd_write_i) ex_forward_b = FORWARD_SEL_WB_RESULT;
    else ex_forward_b = NO_FORWARD_SEL;
  end

  assign id_forward_a = id_wb_rs1_match && wb_is_rd_write_i;
  assign id_forward_b = id_wb_rs2_match && wb_is_rd_write_i;


  // LOAD USE FLUSHES ID/EX AND STALLS IF/ID
  /*****************************************/
  //
  //  OUTPUT ASSIGNMENTS
  //
  /*****************************************/
  // stall conditions :
  // stall ifid on a load use hazard
  // stall ex/mem and mem/wb on a read or write request
  // flush conditions : 
  // flush if/id on a jump or trap
  // flush id/ex on a jump or trap
  // flush ex/mem on a jump or trap
  // flush mem_wb on a trap

  assign id_forward_a_o = id_forward_a;
  assign id_forward_b_o = id_forward_b;
  assign ex_forward_a_sel_o = ex_forward_a;
  assign ex_forward_b_sel_o = ex_forward_b;

  assign if_id_flush_o = mem_jump_taken_i | (ex_trap_valid_i | mem_trap_valid_i | wb_trap_valid_i);
  assign id_ex_flush_o = mem_jump_taken_i | (mem_trap_valid_i | wb_trap_valid_i) | (if_id_stall_o && !id_ex_stall_o);
  assign ex_mem_flush_o = (mem_jump_taken_i && !ex_mem_stall_o) | (mem_trap_valid_i | wb_trap_valid_i) | (id_ex_stall_o && !ex_mem_stall_o);
  assign mem_wb_flush_o = wb_trap_valid_i | (ex_mem_stall_o && !mem_wb_stall_o);

  assign if_id_stall_o = load_use_hazard | id_ex_stall_o;
  assign id_ex_stall_o = ex_mem_stall_o;
  assign ex_mem_stall_o = mem_req_stall | mem_wb_stall_o;
  assign mem_wb_stall_o = mem_req_stall;


endmodule
