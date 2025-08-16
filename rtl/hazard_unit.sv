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

    output logic IF_FLUSH,
    output logic ID_FLUSH,
    output logic EX_FLUSH,
    output logic MEM1_FLUSH,
    output logic MEM2_FLUSH,

    output logic IF_STALL,
    output logic ID_STALL,
    output logic EX_STALL,
    

    // trap logic
    input logic ID_TRAP_VALID,
    input logic EX_TRAP_VALID,
    input logic MEM1_TRAP_VALID,
    input logic MEM2_TRAP_VALID,
    input logic WB_TRAP_VALID,

    input logic AXIL_EN,
    input logic AXIL_DONE_READ,
    input logic AXIL_DONE_WRITE

);
import params_pkg::*;
  logic [2:0] EX_forward_a;
  logic [2:0] EX_forward_b;
  logic ID_forward_a;
  logic ID_forward_b;
  logic load_use_stall;
  logic csr_read_use_stall;
  logic nonzero_ID_rs1;
  logic nonzero_ID_rs2;
  logic ID_rs1_eq_EX_rd;
  logic ID_rs1_eq_MEM1_rd;
  logic ID_rs1_eq_MEM2_rd;
  logic ID_rs2_eq_EX_rd;
  logic ID_rs2_eq_MEM1_rd;
  logic ID_rs2_eq_MEM2_rd;
  logic ID_EX_csr_read_use_stall;
  logic ID_MEM1_csr_read_use_stall;
  logic ID_MEM2_csr_read_use_stall;
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

  // stall if the result of an incomplete CSR read is needed
  assign ID_EX_csr_read_use_stall = (EX_RESULT_SRC == RESULT_SRC_SELECT_CSR_READ_DATA)
  && ((ID_rs1_eq_EX_rd && nonzero_ID_rs1) || ID_rs2_eq_EX_rd  && nonzero_ID_rs2);

  assign ID_MEM1_csr_read_use_stall = (MEM1_RESULT_SRC == RESULT_SRC_SELECT_CSR_READ_DATA)
  && ((ID_rs1_eq_MEM1_rd && nonzero_ID_rs1) || ID_rs2_eq_MEM1_rd  && nonzero_ID_rs2);

  assign ID_MEM2_csr_read_use_stall = (MEM2_RESULT_SRC == RESULT_SRC_SELECT_CSR_READ_DATA)
  && ((ID_rs1_eq_MEM2_rd && nonzero_ID_rs1) || ID_rs2_eq_MEM2_rd  && nonzero_ID_rs2);

  // We must stall if a load instruction is in the execute stage while another instruction 
  // has a matching source register to that write register in the decode stage
  always_comb begin
    load_use_stall = 0;
    if ((EX_RESULT_SRC == RESULT_SRC_SELECT_DMEM_RD_DATA) && ((ID_rs1_eq_EX_rd && nonzero_ID_rs1) || (ID_rs2_eq_EX_rd  && nonzero_ID_rs2)))
      load_use_stall = 1;
  end

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
      EX_forward_a = FORWARD_SEL_MEM1_ALU_RESULT;  
    else if ((EX_RS1_ADDR == MEM2_RD_ADDR) && (EX_RS1_ADDR != 0) && (MEM2_RESULT_SRC == RESULT_SRC_SELECT_DMEM_RD_DATA))
      EX_forward_a = FORWARD_SEL_MEM2_MEM_RDATA;
    else if ((EX_RS1_ADDR == MEM2_RD_ADDR) && (EX_RS1_ADDR != 0))
      EX_forward_a = FORWARD_SEL_MEM2_ALU_RESULT;  
    else if ((EX_RS1_ADDR == WB_RD_ADDR) && (EX_RS1_ADDR != 0))
      EX_forward_a = FORWARD_SEL_WB_RESULT;  
    else EX_forward_a = FORWARD_SEL_NO_FORWARD;  

    if ((EX_RS2_ADDR == MEM1_RD_ADDR) && (EX_RS2_ADDR != 0))
      EX_forward_b = FORWARD_SEL_MEM1_ALU_RESULT;  
    else if ((EX_RS2_ADDR == MEM2_RD_ADDR) && (EX_RS2_ADDR != 0) && (MEM2_RESULT_SRC == RESULT_SRC_SELECT_DMEM_RD_DATA))
      EX_forward_b = FORWARD_SEL_MEM2_MEM_RDATA;
    else if ((EX_RS2_ADDR == MEM2_RD_ADDR) && (EX_RS2_ADDR != 0))
      EX_forward_b = FORWARD_SEL_MEM2_ALU_RESULT;  
    else if ((EX_RS2_ADDR == WB_RD_ADDR) && (EX_RS2_ADDR != 0))
      EX_forward_b = FORWARD_SEL_WB_RESULT;  
    else EX_forward_b = FORWARD_SEL_NO_FORWARD;  
  end

  assign csr_read_use_stall = ID_EX_csr_read_use_stall | ID_MEM1_csr_read_use_stall | ID_MEM2_csr_read_use_stall;
  assign EX_FORWARD_A = EX_forward_a;
  assign EX_FORWARD_B = EX_forward_b;
  always_comb begin
    ID_forward_a = 0;
    ID_forward_b = 0;
    if (ID_RS1_ADDR == WB_RD_ADDR) ID_forward_a = 1;
    if (ID_RS2_ADDR == WB_RD_ADDR) ID_forward_b = 1;
  end


  /*****************************************/
  //
  //  OUTPUT ASSIGNMENTS
  //
  /*****************************************/

  assign ID_FORWARD_A = ID_forward_a;
  assign ID_FORWARD_B = ID_forward_b;

  // if a jump instruction is in EX, and an axil transaction is stalling in MEM1, 
  // the ID flush resulting from a branch hazard must be disabled until the stall ends, or else the branch instruction 
  // will be lost
  // this is avoided for traps by never flushing a stage before the one that has a trap. For example, if 
  // there is a trap in ID, only flush IF once the trap moves to the EX stage. This is only necessary for stages
  // that can be stalled, which would result in the trap being cleared without propagating.
  // insert bubbles for any stages where the previous stage is stalled and the current one is not stalled
  assign IF_FLUSH = EX_PC_SRC | (EX_TRAP_VALID | MEM1_TRAP_VALID | MEM2_TRAP_VALID | WB_TRAP_VALID);
  assign ID_FLUSH = (EX_PC_SRC & ~axil_stall) | (MEM1_TRAP_VALID | MEM2_TRAP_VALID | WB_TRAP_VALID) | (IF_STALL & ~ID_STALL);
  assign EX_FLUSH = MEM2_TRAP_VALID | WB_TRAP_VALID | (ID_STALL & ~EX_STALL);
  assign MEM1_FLUSH = WB_TRAP_VALID;
  assign MEM2_FLUSH = WB_TRAP_VALID;
  // no need to stall if instructions are flushed anyway
  assign IF_STALL = (load_use_stall | csr_read_use_stall) | axil_stall;
  assign ID_STALL = axil_stall;
  assign EX_STALL = axil_stall;

endmodule
