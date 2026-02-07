import riscv_pkg::*;
module hazard_ctrl #(parameter int REG_ADDR_W = 5) (
  // --------------------
  // Register addresses
  // --------------------
  input  logic [REG_ADDR_W-1:0] id_rs1_addr          ,
  input  logic [REG_ADDR_W-1:0] id_rs2_addr          ,
  input  logic [REG_ADDR_W-1:0] ex_q_rs1_addr        ,
  input  logic [REG_ADDR_W-1:0] ex_q_rs2_addr        ,
  input  logic [REG_ADDR_W-1:0] ex_q_rd_addr         ,
  input  logic [REG_ADDR_W-1:0] mem_q_rd_addr        ,
  input  logic [REG_ADDR_W-1:0] wb_q_rd_addr         ,
  // --------------------
  // Control qualifiers
  // --------------------
  input  logic                  ex_q_is_mem_read     ,
  input  logic                  mem_q_is_rd_write    ,
  input  logic                  wb_q_is_rd_write     ,
  input  logic                  mem_q_jump_taken     ,
  input  logic                  mem_q_is_branch      ,
  input  logic                  mem_branch_mispredict,
  input  logic                  id_predict_btaken    ,
  input  logic                  ex_q_trap_valid      ,
  input  logic                  mem_q_trap_valid     ,
  input  logic                  wb_q_trap_valid      ,
  input  logic                  dmem_periph_req      ,
  input  logic                  mem_done_i           ,
  // --------------------
  // Outputs
  // --------------------
  output logic                  if_id_stall          ,
  output logic                  id_ex_stall          ,
  output logic                  ex_mem_stall         ,
  output logic                  mem_wb_stall         ,
  output logic                  if_id_flush          ,
  output logic                  id_ex_flush          ,
  output logic                  ex_mem_flush         ,
  output logic                  mem_wb_flush         ,
  output logic                  id_forward_rs1       ,
  output logic                  id_forward_rs2       ,
  output logic [           1:0] ex_forward_rs1_sel   ,
  output logic [           1:0] ex_forward_rs2_sel
);


  logic load_use_stall;
  logic mem_req_stall ;
  logic jump_flush    ;

  // --------------------
  // Hazard match wires
  // --------------------
  wire id_wb_rs1_match ;
  wire id_wb_rs2_match ;
  wire id_ex_rs1_match ;
  wire id_ex_rs2_match ;
  wire ex_mem_rs1_match;
  wire ex_mem_rs2_match;
  wire ex_wb_rs1_match ;
  wire ex_wb_rs2_match ;

  assign id_wb_rs1_match  = (id_rs1_addr == wb_q_rd_addr)  && |id_rs1_addr;
  assign id_wb_rs2_match  = (id_rs2_addr == wb_q_rd_addr)  && |id_rs2_addr;
  assign id_ex_rs1_match  = (id_rs1_addr == ex_q_rd_addr)  && |id_rs1_addr;
  assign id_ex_rs2_match  = (id_rs2_addr == ex_q_rd_addr)  && |id_rs2_addr;
  assign ex_mem_rs1_match = (ex_q_rs1_addr == mem_q_rd_addr) && |ex_q_rs1_addr;
  assign ex_mem_rs2_match = (ex_q_rs2_addr == mem_q_rd_addr) && |ex_q_rs2_addr;
  assign ex_wb_rs1_match  = (ex_q_rs1_addr == wb_q_rd_addr)  && |ex_q_rs1_addr;
  assign ex_wb_rs2_match  = (ex_q_rs2_addr == wb_q_rd_addr)  && |ex_q_rs2_addr;

  // --------------------
  // Stall logic
  // --------------------
  assign load_use_stall = ex_q_is_mem_read &&
    (id_ex_rs1_match || id_ex_rs2_match);

  assign mem_req_stall = dmem_periph_req && !mem_done_i;

  // --------------------
  // Forwarding logic
  // --------------------
  always_comb begin
    // rs1
    if (ex_mem_rs1_match && mem_q_is_rd_write)
      ex_forward_rs1_sel = FORWARD_SEL_MEM_RESULT;
    else if (ex_wb_rs1_match && wb_q_is_rd_write)
      ex_forward_rs1_sel = FORWARD_SEL_WB_RESULT;
    else
      ex_forward_rs1_sel = NO_FORWARD_SEL;

    // rs2
    if (ex_mem_rs2_match && mem_q_is_rd_write)
      ex_forward_rs2_sel = FORWARD_SEL_MEM_RESULT;
    else if (ex_wb_rs2_match && wb_q_is_rd_write)
      ex_forward_rs2_sel = FORWARD_SEL_WB_RESULT;
    else
      ex_forward_rs2_sel = NO_FORWARD_SEL;
  end

  assign id_forward_rs1 = id_wb_rs1_match && wb_q_is_rd_write;
  assign id_forward_rs2 = id_wb_rs2_match && wb_q_is_rd_write;

  // --------------------
  // Flush logic
  // --------------------
  assign jump_flush = mem_q_jump_taken && !mem_q_is_branch;

  assign if_id_flush =
    mem_branch_mispredict
    || jump_flush
    || (id_predict_btaken && !id_ex_stall && !if_id_stall)
    || (ex_q_trap_valid || mem_q_trap_valid || wb_q_trap_valid);

  assign id_ex_flush =
    mem_branch_mispredict
    || jump_flush
    || (mem_q_trap_valid || wb_q_trap_valid);

  assign ex_mem_flush =
    (mem_branch_mispredict && !mem_wb_stall)
    || (jump_flush            && !mem_wb_stall)
    || (mem_q_trap_valid || wb_q_trap_valid);

  assign mem_wb_flush = wb_q_trap_valid;

  // --------------------
  // Pipeline stall chain
  // --------------------
  assign if_id_stall  = load_use_stall || id_ex_stall;
  assign id_ex_stall  = ex_mem_stall;
  assign ex_mem_stall = mem_req_stall || mem_wb_stall;
  // stall the mem/wb register during a memory transaction
  assign mem_wb_stall = mem_req_stall;
endmodule
