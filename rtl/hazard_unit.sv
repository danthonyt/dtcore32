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

    output logic ID_FLUSH,
    output logic EX_FLUSH,
    output logic MEM1_FLUSH,
    output logic MEM2_FLUSH,
    output logic WB_FLUSH,

    output logic IF_STALL,
    output logic ID_STALL,
    // for axil
    output logic EX_STALL,
    output logic MEM1_STALL,
    

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
  // flushes caused by traps will override stalls
  // flushes caused by a jump will override stalls
  // 
  assign ID_FLUSH = EX_PC_SRC | (EX_TRAP_VALID | MEM1_TRAP_VALID | MEM2_TRAP_VALID | WB_TRAP_VALID);
  assign EX_FLUSH = (EX_PC_SRC & ~EX_STALL) | (MEM1_TRAP_VALID | MEM2_TRAP_VALID | WB_TRAP_VALID);
  assign MEM1_FLUSH = MEM2_TRAP_VALID | WB_TRAP_VALID;
  assign MEM2_FLUSH = WB_TRAP_VALID;
  assign WB_FLUSH = WB_TRAP_VALID;
  // no need to stall if instructions are flushed anyway
  assign IF_STALL = ((load_use_stall | csr_read_use_stall) & ~EX_PC_SRC) | axil_stall_i;
  assign ID_STALL = ((load_use_stall | csr_read_use_stall) & ~EX_PC_SRC) | axil_stall_i;
  assign EX_STALL = axil_stall;
  assign MEM1_STALL = axil_stall;

endmodule