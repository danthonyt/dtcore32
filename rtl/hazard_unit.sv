module hazard_unit (
    //Forwarding
    input logic [4:0] EX_RS1_ADDR,
    input logic [4:0] EX_RS2_ADDR,
    input logic [4:0] MEM_RD_ADDR,
    input logic [4:0] WB_RD_ADDR,
    //Stalling
    input logic [1:0] EX_RESULT_SRC,
    input logic [1:0] MEM_RESULT_SRC,
    input logic [4:0] ID_RS1_ADDR,
    input logic [4:0] ID_RS2_ADDR,
    input logic [4:0] EX_RD_ADDR,
    //branch control hazard
    input logic EX_PC_SRC,
    // axi lite stall
    output logic [2:0] EX_FORWARD_A,
    output logic [2:0] EX_FORWARD_B,
    output logic ID_FORWARD_A,
    output logic ID_FORWARD_B,

    output logic IF_ID_FLUSH,
    output logic ID_EX_FLUSH,
    output logic EX_MEM_FLUSH,
    output logic MEM_WB_FLUSH,

    output logic IF_ID_STALL,
    output logic ID_EX_STALL,
    output logic EX_MEM_STALL,
    output logic MEM_WB_STALL,
    

    // trap logic
    input logic EX_TRAP_VALID,
    input logic MEM_TRAP_VALID,
    input logic WB_TRAP_VALID,

    input logic AXIL_EN,
    input logic AXIL_DONE_READ,
    input logic AXIL_DONE_WRITE

);
  import params_pkg::*;
  logic [2:0] ex_forward_a;
  logic [2:0] ex_forward_b;
  logic if_forward_a;
  logic id_forward_b;
  logic load_use_hazard;
  logic nonzero_ID_rs1;
  logic nonzero_ID_rs2;
  logic id_ex_rs1_match;
  logic id_mem_rs1_match;
  logic id_ex_rs2_match;
  logic id_mem_rs2_match;
  logic axil_req;
  logic ex_mem_rs2_match;
  logic ex_mem_rs1_match;
  logic ex_wb_rs2_match;
  logic ex_wb_rs1_match;
  logic axil_stall;
  assign nonzero_ID_rs1 = |ID_RS1_ADDR;
  assign nonzero_ID_rs2 = |ID_RS2_ADDR;
  assign id_ex_rs1_match = (ID_RS1_ADDR == EX_RD_ADDR);
  assign id_mem_rs1_match = (ID_RS1_ADDR == MEM_RD_ADDR);
  assign id_ex_rs2_match = (ID_RS2_ADDR == EX_RD_ADDR);
  assign id_mem_rs2_match = (ID_RS2_ADDR == MEM_RD_ADDR);
  assign ex_mem_rs1_match = ((EX_RS1_ADDR == MEM_RD_ADDR) && (EX_RS1_ADDR != 0));
  assign ex_mem_rs2_match = ((EX_RS2_ADDR == MEM_RD_ADDR) && (EX_RS2_ADDR != 0));

  /*****************************************/
  //
  //  STALL LOGIC
  //
  /*****************************************/
  // stall if axil transaction is still not done
  assign axil_req = AXIL_EN & ~(AXIL_DONE_READ | AXIL_DONE_WRITE);

  // We must stall if a load instruction is in the execute stage while another instruction 
  // has a matching source register to that write register in the decode stage
  assign load_use_hazard = ((EX_RESULT_SRC == RESULT_SEL_MEM_DATA) && ((id_ex_rs1_match && nonzero_ID_rs1)
   || (id_ex_rs2_match && nonzero_ID_rs2))) ? 1 : 0;

  /*****************************************/
  //
  //  FORWARDING LOGIC
  //
  /*****************************************/

  //if either source register matches a register we are writing to in a previous
  //instruction we must forward that value from the previous instruction so the updated
  //value is used.
  always_comb begin
    if (ex_mem_rs1_match && (MEM_RESULT_SRC == RESULT_SEL_MEM_DATA))
      ex_forward_a = FORWARD_SEL_MEM_LOAD_RDATA;
    else if (ex_mem_rs1_match)
      ex_forward_a = FORWARD_SEL_MEM_ALU_RESULT;
    else if (ex_wb_rs1_match)
      ex_forward_a = FORWARD_SEL_WB_RESULT;
    else ex_forward_a = NO_FORWARD_SEL;

    if (ex_mem_rs2_match && (MEM_RESULT_SRC == RESULT_SEL_MEM_DATA))
      ex_forward_b = FORWARD_SEL_MEM_LOAD_RDATA;
    else if (ex_mem_rs2_match)
      ex_forward_b = FORWARD_SEL_MEM_ALU_RESULT;
    else if (ex_wb_rs2_match)
      ex_forward_b = FORWARD_SEL_WB_RESULT;
    else ex_forward_b = NO_FORWARD_SEL;
  end

  assign EX_FORWARD_A = ex_forward_a;
  assign EX_FORWARD_B = ex_forward_b;
  assign if_forward_a = (ID_RS1_ADDR == WB_RD_ADDR);
  assign id_forward_b = (ID_RS2_ADDR == WB_RD_ADDR);


  // LOAD USE FLUSHES ID/EX AND STALLS IF/ID
  /*****************************************/
  //
  //  OUTPUT ASSIGNMENTS
  //
  /*****************************************/

  assign ID_FORWARD_A = if_forward_a;
  assign ID_FORWARD_B = id_forward_b;

  // if a jump instruction is in EX, and an axil transaction is stalling in MEM1, 
  // the ID flush resulting from a branch hazard must be disabled until the stall ends, or else the branch instruction 
  // will be lost
  // this is avoided for traps by never flushing a stage before the one that has a trap. For example, if 
  // there is a trap in ID, only flush IF once the trap moves to the EX stage. This is only necessary for stages
  // that can be stalled, which would result in the trap being cleared without propagating.
  // insert bubbles for any stages where the previous stage is stalled and the current one is not stalled
  assign IF_ID_FLUSH = (EX_PC_SRC & ~axil_req) | (EX_TRAP_VALID | MEM_TRAP_VALID | WB_TRAP_VALID);
  assign ID_EX_FLUSH = ((EX_PC_SRC | load_use_hazard) & ~axil_req) |(MEM_TRAP_VALID | WB_TRAP_VALID);
  assign EX_MEM_FLUSH = MEM_TRAP_VALID | WB_TRAP_VALID;
  assign MEM_WB_FLUSH = WB_TRAP_VALID;
  // no need to stall if instructions are flushed anyway
  assign IF_ID_STALL = load_use_hazard | axil_req;
  assign ID_EX_STALL = axil_req;
  assign EX_MEM_STALL = axil_req;
  assign MEM_WB_STALL = axil_req;

endmodule
