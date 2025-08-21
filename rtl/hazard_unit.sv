module hazard_unit (
    //Forwarding
    input logic [4:0] EX_RS1_ADDR,
    input logic [4:0] EX_RS2_ADDR,
    input logic [4:0] MEM1_RD_ADDR,
    input logic [4:0] MEM2_RD_ADDR,
    input logic [4:0] WB_RD_ADDR,
    //Stalling
    input logic [1:0] EX_RESULT_SRC,
    input logic [1:0] MEM1_RESULT_SRC,
    input logic [1:0] MEM2_RESULT_SRC,
    input logic [4:0] ID_RS1_ADDR,
    input logic [4:0] ID_RS2_ADDR,
    input logic [4:0] EX_RD_ADDR,
    //branch control hazard
    input logic EX_PC_SRC,
    output logic [2:0] EX_FORWARD_A,
    output logic [2:0] EX_FORWARD_B,
    output logic ID_FORWARD_A,
    output logic ID_FORWARD_B,

    output logic IF_ID_FLUSH,
    output logic ID_EX_FLUSH,
    output logic EX_MEM1_FLUSH,
    output logic MEM1_MEM2_FLUSH,
    output logic MEM2_WB_FLUSH,

    output logic IF_ID_STALL,
    output logic ID_EX_STALL,
    output logic EX_MEM1_STALL,
    output logic MEM1_MEM2_STALL,
    output logic MEM2_WB_STALL,
    

    // trap logic
    input logic EX_TRAP_VALID,
    input logic MEM1_TRAP_VALID,
    input logic MEM2_TRAP_VALID,
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
  logic load_use_stall;
  logic nonzero_ID_rs1;
  logic nonzero_ID_rs2;
  logic ID_rs1_eq_EX_rd;
  logic ID_rs1_eq_MEM1_rd;
  logic ID_rs1_eq_MEM2_rd;
  logic ID_rs2_eq_EX_rd;
  logic ID_rs2_eq_MEM1_rd;
  logic ID_rs2_eq_MEM2_rd;
  logic axil_stall;
  assign nonzero_ID_rs1 = |ID_RS1_ADDR;
  assign nonzero_ID_rs2 = |ID_RS2_ADDR;
  assign ID_rs1_eq_EX_rd = (ID_RS1_ADDR == EX_RD_ADDR) ? 1 : 0;
  assign ID_rs1_eq_MEM1_rd = (ID_RS1_ADDR == MEM1_RD_ADDR) ? 1 : 0;
  assign ID_rs1_eq_MEM2_rd = (ID_RS1_ADDR == MEM2_RD_ADDR) ? 1 : 0;
  assign ID_rs2_eq_EX_rd = (ID_RS2_ADDR == EX_RD_ADDR) ? 1 : 0;
  assign ID_rs2_eq_MEM1_rd = (ID_RS2_ADDR == MEM1_RD_ADDR) ? 1 : 0;
  assign ID_rs2_eq_MEM2_rd = (ID_RS2_ADDR == MEM2_RD_ADDR) ? 1 : 0;

  /*****************************************/
  //
  //  STALL LOGIC
  //
  /*****************************************/
  // stall if axil transaction is still not done
  assign axil_stall = AXIL_EN & ~(AXIL_DONE_READ | AXIL_DONE_WRITE);

  // We must stall if a load instruction is in the execute stage while another instruction 
  // has a matching source register to that write register in the decode stage
  assign load_use_stall = ((EX_RESULT_SRC == RESULT_SRC_SELECT_DMEM_RD_DATA) && ((ID_rs1_eq_EX_rd && nonzero_ID_rs1)
   || (ID_rs2_eq_EX_rd && nonzero_ID_rs2))) ? 1 : 0;

  /*****************************************/
  //
  //  FORWARDING LOGIC
  //
  /*****************************************/

  //if either source register matches a register we are writing to in a previous
  //instruction we must forward that value from the previous instruction so the updated
  //value is used.
  always_comb begin
    if ((EX_RS1_ADDR == MEM1_RD_ADDR) && (EX_RS1_ADDR != 0))
      ex_forward_a = FORWARD_SEL_MEM1_ALU_RESULT;
    else if ((EX_RS1_ADDR == MEM2_RD_ADDR) && (EX_RS1_ADDR != 0) && (MEM2_RESULT_SRC == RESULT_SRC_SELECT_DMEM_RD_DATA))
      ex_forward_a = FORWARD_SEL_MEM2_MEM_RDATA;
    else if ((EX_RS1_ADDR == MEM2_RD_ADDR) && (EX_RS1_ADDR != 0))
      ex_forward_a = FORWARD_SEL_MEM2_ALU_RESULT;
    else if ((EX_RS1_ADDR == WB_RD_ADDR) && (EX_RS1_ADDR != 0))
      ex_forward_a = FORWARD_SEL_WB_RESULT;
    else ex_forward_a = FORWARD_SEL_NO_FORWARD;

    if ((EX_RS2_ADDR == MEM1_RD_ADDR) && (EX_RS2_ADDR != 0))
      ex_forward_b = FORWARD_SEL_MEM1_ALU_RESULT;
    else if ((EX_RS2_ADDR == MEM2_RD_ADDR) && (EX_RS2_ADDR != 0) && (MEM2_RESULT_SRC == RESULT_SRC_SELECT_DMEM_RD_DATA))
      ex_forward_b = FORWARD_SEL_MEM2_MEM_RDATA;
    else if ((EX_RS2_ADDR == MEM2_RD_ADDR) && (EX_RS2_ADDR != 0))
      ex_forward_b = FORWARD_SEL_MEM2_ALU_RESULT;
    else if ((EX_RS2_ADDR == WB_RD_ADDR) && (EX_RS2_ADDR != 0))
      ex_forward_b = FORWARD_SEL_WB_RESULT;
    else ex_forward_b = FORWARD_SEL_NO_FORWARD;
  end

  assign EX_FORWARD_A = ex_forward_a;
  assign EX_FORWARD_B = ex_forward_b;
  assign if_forward_a = (ID_RS1_ADDR == WB_RD_ADDR) ? 1 : 0;
  assign id_forward_b = (ID_RS2_ADDR == WB_RD_ADDR) ? 1 : 0;


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
  assign IF_ID_FLUSH = (EX_PC_SRC & ~axil_stall) | (EX_TRAP_VALID | MEM1_TRAP_VALID | MEM2_TRAP_VALID | WB_TRAP_VALID);
  assign ID_EX_FLUSH = ((EX_PC_SRC | load_use_stall) & ~axil_stall) |(MEM1_TRAP_VALID | MEM2_TRAP_VALID | WB_TRAP_VALID);
  assign EX_MEM1_FLUSH = MEM2_TRAP_VALID | WB_TRAP_VALID;
  assign MEM1_MEM2_FLUSH = WB_TRAP_VALID;
  assign MEM2_WB_FLUSH = WB_TRAP_VALID;
  // no need to stall if instructions are flushed anyway
  assign IF_ID_STALL = load_use_stall | axil_stall;
  assign ID_EX_STALL = axil_stall;
  assign EX_MEM1_STALL = axil_stall;
  assign MEM1_MEM2_STALL = axil_stall;
  assign MEM2_WB_STALL = axil_stall;

endmodule
