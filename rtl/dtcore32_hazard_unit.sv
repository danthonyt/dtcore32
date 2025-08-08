module dtcore32_hazard_unit (
    //Forwarding
    input logic [4:0] EX_rs1_addr_i,
    input logic [4:0] EX_rs2_addr_i,
    input logic [4:0] MEM1_rd_addr_i,
    input logic [4:0] MEM2_rd_addr_i,
    input logic [4:0] WB_rd_addr_i,
    //Stalling
    input logic [1:0] EX_result_src_i,
    input logic [1:0] MEM1_result_src_i,
    input logic [1:0] MEM2_result_src_i,
    input logic [4:0] ID_rs1_addr_i,
    input logic [4:0] ID_rs2_addr_i,
    input logic [4:0] EX_rd_addr_i,
    //branch control hazard
    input logic EX_pc_src_i,
    output logic [2:0] EX_forward_a_o,
    output logic [2:0] EX_forward_b_o,
    output logic ID_forward_a_o,
    output logic ID_forward_b_o,

    output logic ID_flush_o,
    output logic EX_flush_o,
    output logic MEM1_flush_o,
    output logic MEM2_flush_o,
    output logic WB_flush_o,

    output logic IF_stall_o,
    output logic ID_stall_o,

    // trap logic
    input logic ID_trap_valid_i,
    input logic EX_trap_valid_i,
    input logic MEM1_trap_valid_i,
    input logic MEM2_trap_valid_i,
    input logic WB_trap_valid_i

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
  assign nonzero_ID_rs1 = |ID_rs1_addr_i;
  assign nonzero_ID_rs2 = |ID_rs2_addr_i;
  assign ID_rs1_eq_EX_rd = (ID_rs1_addr_i == EX_rd_addr_i) ? 1 : 0;
  assign ID_rs1_eq_MEM1_rd = (ID_rs1_addr_i == MEM1_rd_addr_i) ? 1 : 0;
  assign ID_rs1_eq_MEM2_rd = (ID_rs1_addr_i == MEM2_rd_addr_i) ? 1 : 0;
  assign ID_rs2_eq_EX_rd = (ID_rs2_addr_i == EX_rd_addr_i) ? 1 : 0;
  assign ID_rs2_eq_MEM1_rd = (ID_rs2_addr_i == MEM1_rd_addr_i) ? 1 : 0;
  assign ID_rs2_eq_MEM2_rd = (ID_rs2_addr_i == MEM2_rd_addr_i) ? 1 : 0;


  assign ID_EX_csr_read_use_stall = (EX_result_src_i == RESULT_SRC_SELECT_CSR_READ_DATA)
  && ((ID_rs1_eq_EX_rd && nonzero_ID_rs1) || ID_rs2_eq_EX_rd  && nonzero_ID_rs2);

  assign ID_MEM1_csr_read_use_stall = (MEM1_result_src_i == RESULT_SRC_SELECT_CSR_READ_DATA)
  && ((ID_rs1_eq_MEM1_rd && nonzero_ID_rs1) || ID_rs2_eq_MEM1_rd  && nonzero_ID_rs2);

  assign ID_MEM2_csr_read_use_stall = (MEM2_result_src_i == RESULT_SRC_SELECT_CSR_READ_DATA)
  && ((ID_rs1_eq_MEM2_rd && nonzero_ID_rs1) || ID_rs2_eq_MEM2_rd  && nonzero_ID_rs2);
  //if either source register matches a register we are writing to in a previous
  //instruction we must forward that value from the previous instruction so the updated
  //value is used.
  always_comb begin
    if ((EX_rs1_addr_i == MEM1_rd_addr_i) && (EX_rs1_addr_i != 0))
      EX_forward_a = FORWARD_SEL_MEM1_ALU_RESULT;  
    else if ((EX_rs1_addr_i == MEM2_rd_addr_i) && (EX_rs1_addr_i != 0) && (MEM2_result_src_i == RESULT_SRC_SELECT_DMEM_RD_DATA))
      EX_forward_a = FORWARD_SEL_MEM2_MEM_RDATA;
    else if ((EX_rs1_addr_i == MEM2_rd_addr_i) && (EX_rs1_addr_i != 0))
      EX_forward_a = FORWARD_SEL_MEM2_ALU_RESULT;  
    else if ((EX_rs1_addr_i == WB_rd_addr_i) && (EX_rs1_addr_i != 0))
      EX_forward_a = FORWARD_SEL_WB_RESULT;  
    else EX_forward_a = FORWARD_SEL_NO_FORWARD;  

    if ((EX_rs2_addr_i == MEM1_rd_addr_i) && (EX_rs2_addr_i != 0))
      EX_forward_b = FORWARD_SEL_MEM1_ALU_RESULT;  
    else if ((EX_rs2_addr_i == MEM2_rd_addr_i) && (EX_rs2_addr_i != 0) && (MEM2_result_src_i == RESULT_SRC_SELECT_DMEM_RD_DATA))
      EX_forward_b = FORWARD_SEL_MEM2_MEM_RDATA;
    else if ((EX_rs2_addr_i == MEM2_rd_addr_i) && (EX_rs2_addr_i != 0))
      EX_forward_b = FORWARD_SEL_MEM2_ALU_RESULT;  
    else if ((EX_rs2_addr_i == WB_rd_addr_i) && (EX_rs2_addr_i != 0))
      EX_forward_b = FORWARD_SEL_WB_RESULT;  
    else EX_forward_b = FORWARD_SEL_NO_FORWARD;  
  end

  always_comb begin
    //We must stall if a load instruction is in the execute stage while another instruction has a matching source register to that write register in the decode stage
    if ((EX_result_src_i == RESULT_SRC_SELECT_DMEM_RD_DATA) && ((ID_rs1_eq_EX_rd && nonzero_ID_rs1) || (ID_rs2_eq_EX_rd  && nonzero_ID_rs2)))
      load_use_stall = 1;
    else load_use_stall = 0;
  end

  assign csr_read_use_stall = ID_EX_csr_read_use_stall | ID_MEM1_csr_read_use_stall | ID_MEM2_csr_read_use_stall;
  assign EX_forward_a_o = EX_forward_a;
  assign EX_forward_b_o = EX_forward_b;
  always_comb begin
    ID_forward_a = 0;
    ID_forward_b = 0;
    if (ID_rs1_addr_i == WB_rd_addr_i) ID_forward_a = 1;
    if (ID_rs2_addr_i == WB_rd_addr_i) ID_forward_b = 1;
  end


  assign ID_forward_a_o = ID_forward_a;
  assign ID_forward_b_o = ID_forward_b;
  assign ID_flush_o = EX_pc_src_i | (ID_trap_valid_i & ~ID_stall_o) | (EX_trap_valid_i | MEM1_trap_valid_i | MEM2_trap_valid_i | WB_trap_valid_i);
  assign EX_flush_o = EX_pc_src_i | (EX_trap_valid_i | MEM1_trap_valid_i | MEM2_trap_valid_i | WB_trap_valid_i);
  assign MEM1_flush_o = MEM1_trap_valid_i | MEM2_trap_valid_i | WB_trap_valid_i;
  assign MEM2_flush_o = MEM2_trap_valid_i | WB_trap_valid_i;
  assign WB_flush_o = WB_trap_valid_i;
  // no need to stall if instructions are flushed anyway
  assign IF_stall_o = (load_use_stall | csr_read_use_stall) & ~EX_pc_src_i;
  assign ID_stall_o = (load_use_stall | csr_read_use_stall) & ~EX_pc_src_i;

endmodule