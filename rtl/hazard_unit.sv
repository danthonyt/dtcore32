//===========================================================
// Project    : RISC-V CPU
// File       : hazard_unit.sv
// Module     : hazard_unit
// Description: Pipeline hazard detection and forwarding unit.
//              Handles data hazards, control hazards, stalls, and
//              flushes. Generates forwarding signals for ALU inputs
//              and stall/flush signals for pipeline registers.
//
// Inputs:
//   mem_is_rd_write_i      - High if MEM stage writes to destination register
//   wb_is_rd_write_i       - High if WB stage writes to destination register
//   id_rs1_addr_i          - Source register 1 address in ID stage
//   id_rs2_addr_i          - Source register 2 address in ID stage
//   ex_rs1_addr_i          - Source register 1 address in EX stage
//   ex_rs2_addr_i          - Source register 2 address in EX stage
//   ex_rd_addr_i           - Destination register address in EX stage
//   mem_rd_addr_i          - Destination register address in MEM stage
//   wb_rd_addr_i           - Destination register address in WB stage
//   mem_jump_taken_i       - High if branch/jump taken in MEM stage
//   mem_branch_mispredict_i - High if branch prediction was incorrect
//   mem_is_branch_i        - High if branch instruction in MEM stage
//   mem_req_i              - Memory request signal
//   mem_done_i             - Memory transaction completion
//   ex_is_mem_read_i       - High if EX stage instruction reads memory
//   ex_trap_valid_i        - High if trap exists in EX stage
//   mem_trap_valid_i       - High if trap exists in MEM stage
//   wb_trap_valid_i        - High if trap exists in WB stage
//
// Outputs:
//   id_forward_a_o         - Forwarding select for ID stage rs1
//   id_forward_b_o         - Forwarding select for ID stage rs2
//   ex_forward_a_sel_o     - Forwarding selection for EX stage rs1
//   ex_forward_b_sel_o     - Forwarding selection for EX stage rs2
//   if_id_flush_o          - Flush signal for IF/ID pipeline register
//   id_ex_flush_o          - Flush signal for ID/EX pipeline register
//   ex_mem_flush_o         - Flush signal for EX/MEM pipeline register
//   mem_wb_flush_o         - Flush signal for MEM/WB pipeline register
//   if_id_stall_o          - Stall signal for IF/ID pipeline register
//   id_ex_stall_o          - Stall signal for ID/EX pipeline register
//   ex_mem_stall_o         - Stall signal for EX/MEM pipeline register
//   mem_wb_stall_o         - Stall signal for MEM/WB pipeline register
//
// Notes:
//   - Implements both forwarding and hazard detection logic to avoid
//     data hazards and control hazards in the pipeline.
//   - Generates flush and stall signals to correctly handle jumps,
//     branches, memory delays, and traps.
//
// Author     : David Torres
// Date       : 2025-09-16
//===========================================================

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
    input logic mem_is_branch_i,
    // mem signals
    input logic mem_req_i,
    input logic mem_done_i,
    input logic mem_branch_mispredict_i,
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
  logic load_use_stall;
  logic id_wb_rs1_match;
  logic id_wb_rs2_match;
  logic id_ex_rs1_match;
  logic id_ex_rs2_match;
  logic ex_mem_rs2_match;
  logic ex_mem_rs1_match;
  logic ex_wb_rs2_match;
  logic ex_wb_rs1_match;
  logic jump_flush;
  logic branch_mispredict_flush;
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
  assign load_use_stall = (ex_is_mem_read_i && (id_ex_rs1_match || id_ex_rs2_match));

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

  /*****************************************/
  //
  //  OUTPUT ASSIGNMENTS
  //
  /*****************************************/

  assign id_forward_a_o = id_forward_a;
  assign id_forward_b_o = id_forward_b;
  assign ex_forward_a_sel_o = ex_forward_a;
  assign ex_forward_b_sel_o = ex_forward_b;
  assign branch_mispredict_flush = mem_branch_mispredict_i;
  assign jump_flush = mem_jump_taken_i && !mem_is_branch_i;

  // flush if/id register on a mispredicted branch, a jump, or an instruction trap
  assign if_id_flush_o = branch_mispredict_flush 
  || jump_flush
  || (ex_trap_valid_i || mem_trap_valid_i || wb_trap_valid_i);

  // flush id/ex register on a mispredicted branch, a jump, an instruction trap,
  // or the previous stage is stalled and the register is not stalled
  assign id_ex_flush_o = branch_mispredict_flush 
  || jump_flush
  || (mem_trap_valid_i || wb_trap_valid_i) 
  || (if_id_stall_o && !id_ex_stall_o);

  // flush ex/mem flush on a mispredicted branch, a jump, an instruction trap,
  // or the previous stage is stalled and the register is not stalled
  assign ex_mem_flush_o = (branch_mispredict_flush && !ex_mem_stall_o)
  || (jump_flush && !ex_mem_stall_o) 
  || (mem_trap_valid_i || wb_trap_valid_i) 
  || (id_ex_stall_o && !ex_mem_stall_o);

  // flush mem/wb register if a trap instruction is committed, or 
  // the previous stage is stalled and the register is not stalled
  assign mem_wb_flush_o = wb_trap_valid_i || (ex_mem_stall_o && !mem_wb_stall_o);

  // stall the if/id register on a load use hazard, or the next
  // stage is stalled
  assign if_id_stall_o = load_use_stall || id_ex_stall_o;

  // stall the id/ex register if the next stage is stalled
  assign id_ex_stall_o = ex_mem_stall_o;

  // stall the ex/mem register during a memory transaction,
  // or the next stage is stalled
  assign ex_mem_stall_o = mem_req_stall || mem_wb_stall_o;

  // stall the mem/wb register during a memory transaction
  assign mem_wb_stall_o = mem_req_stall;


endmodule
