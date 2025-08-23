
module dtcore32 #(
    parameter DMEM_ADDR_WIDTH = 10,
    parameter IMEM_ADDR_WIDTH = 10,
    parameter AXIL_ADDR_WIDTH = 32,
    parameter AXIL_BUS_WIDTH  = 32
) (
    input  logic                       CLK,
    input  logic                       RST,
    input  logic [               31:0] IMEM_RDATA,
    input  logic [               31:0] DMEM_RDATA,
`ifdef RISCV_FORMAL
    output logic                       rvfi_valid,
    output logic [               63:0] rvfi_order,
    output logic [               31:0] rvfi_insn,
    output logic                       rvfi_trap,
    output logic                       rvfi_halt,
    output logic                       rvfi_intr,
    output logic [                1:0] rvfi_mode,
    output logic [                1:0] rvfi_ixl,
    output logic [                4:0] rvfi_rs1_addr,
    output logic [                4:0] rvfi_rs2_addr,
    output logic [               31:0] rvfi_rs1_rdata,
    output logic [               31:0] rvfi_rs2_rdata,
    output logic [                4:0] rvfi_rd_addr,
    output logic [               31:0] rvfi_rd_wdata,
    output logic [               31:0] rvfi_pc_rdata,
    output logic [               31:0] rvfi_pc_wdata,
    output logic [               31:0] rvfi_mem_addr,
    output logic [                3:0] rvfi_mem_rmask,
    output logic [                3:0] rvfi_mem_wmask,
    output logic [               31:0] rvfi_mem_rdata,
    output logic [               31:0] rvfi_mem_wdata,
    output logic [               63:0] rvfi_csr_mcycle_rmask,
    output logic [               63:0] rvfi_csr_mcycle_wmask,
    output logic [               63:0] rvfi_csr_mcycle_rdata,
    output logic [               63:0] rvfi_csr_mcycle_wdata,
    output logic [               63:0] rvfi_csr_minstret_rmask,
    output logic [               63:0] rvfi_csr_minstret_wmask,
    output logic [               63:0] rvfi_csr_minstret_rdata,
    output logic [               63:0] rvfi_csr_minstret_wdata,
    output logic [               31:0] rvfi_csr_mcause_rmask,
    output logic [               31:0] rvfi_csr_mcause_wmask,
    output logic [               31:0] rvfi_csr_mcause_rdata,
    output logic [               31:0] rvfi_csr_mcause_wdata,
    output logic [               31:0] rvfi_csr_mepc_rmask,
    output logic [               31:0] rvfi_csr_mepc_wmask,
    output logic [               31:0] rvfi_csr_mepc_rdata,
    output logic [               31:0] rvfi_csr_mepc_wdata,
    output logic [               31:0] rvfi_csr_mtvec_rmask,
    output logic [               31:0] rvfi_csr_mtvec_wmask,
    output logic [               31:0] rvfi_csr_mtvec_rdata,
    output logic [               31:0] rvfi_csr_mtvec_wdata,
`endif
    output logic [IMEM_ADDR_WIDTH-1:0] IMEM_ADDR,
    output logic [DMEM_ADDR_WIDTH-1:0] DMEM_ADDR,
    output logic [               31:0] DMEM_WDATA,
    output logic [                3:0] DMEM_WMASK,
    output logic                       IMEM_EN,
    output logic                       DMEM_EN,
    // axi lite master interface
    output logic                       AXIL_START_READ,
    output logic                       AXIL_START_WRITE,
    input  logic                       AXIL_DONE_READ,
    input  logic                       AXIL_DONE_WRITE,
    input  logic                       AXIL_BUSY_READ,
    input  logic                       AXIL_BUSY_WRITE,

    // peripheral interface
    // put on the axi line
    output logic [AXIL_ADDR_WIDTH-1:0] AXIL_TRANSACTION_WRADDR,
    output logic [AXIL_BUS_WIDTH-1:0] AXIL_TRANSACTION_WRDATA,
    output logic [(AXIL_BUS_WIDTH/8)-1:0] AXIL_TRANSACTION_WSTRB,
    output logic [AXIL_ADDR_WIDTH-1:0] AXIL_TRANSACTION_RADDR,
    // taken from the axi line
    input logic [AXIL_BUS_WIDTH-1:0] AXIL_TRANSACTION_RDATA
);
  /////////////////////////////////////////////
  //
  //  LOCAL PARAMETERS
  //
  //
  ////////////////////////////////////////////
  import params_pkg::*;

  ///////////////////////////////////////////////
  //
  //  SIGNAL DECLARATIONS
  //
  //
  ///////////////////////////////////////////////

  //////////////////////////////////////
  //
  //
  //
  //
  // INSTRUCTION FETCH SIGNALS
  //
  //
  //
  //
  ///////////////////////////////////////

  logic [31:0] if_a_pc_rdata_r;
  logic [31:0] if_a_pc_rdata_comb;
  logic if_a_valid_insn_r;
  logic if_a_valid_insn_comb;
  logic if_b_valid_insn_r;
  logic if_a_intr_r;
  logic if_a_intr_comb;
  logic if_b_intr_r;
  logic [31:0] if_b_pc_rdata_r;
  logic [31:0] if_b_pc_plus_4_r;
  logic [31:0] next_pc_comb;
  logic [31:0] trap_handler_addr_q;

  rvfi_t if_rvfi;
  rvfi_t id_rvfi;
  rvfi_t ex_rvfi;
  rvfi_t mem_rvfi;
  rvfi_t wb_rvfi;

  //////////////////////////////////////
  //
  //
  //
  //
  // INSTRUCTION DECODE SIGNALS
  //
  //
  //
  //
  ///////////////////////////////////////
  trap_info_t id_trap_d;
  logic [31:0] id_rs1_rdata_d;
  logic [31:0] id_rs1_rfile_rdata_comb;
  logic [31:0] id_rs2_rdata_d;
  logic [31:0] id_rs2_rfile_rdata_comb;
  logic [4:0] id_rs1_addr_d;
  logic [4:0] id_rs2_addr_d;
  logic [11:0] id_csr_addr_d;
  logic [31:0] id_imm_ext_d;
  logic [4:0] id_rd_addr_d;
  alu_control_t id_alu_control_d;

  // directly taken from instruction word
  logic [6:0] id_op_comb;
  logic [2:0] id_funct3_comb;
  logic id_funct7b5_comb;
  logic [6:0] id_funct7_comb;
  logic [11:0] id_funct12_comb;
  logic [1:0] id_alu_op_comb;
  logic id_rtype_alt_comb;
  logic id_itype_alt_comb;
  logic id_forward_a_comb;
  logic id_forward_b_comb;
  logic id_rs1_valid_comb;
  logic id_rs2_valid_comb;
  logic id_rd_valid_comb;
  logic [30:0] id_maindec_mcause_comb;
  logic id_maindec_trap_valid_comb;

  mem_op_t id_mem_op_d;
  cf_op_t id_cf_op_d;
  csr_op_t id_csr_op_d;
  imm_ext_op id_imm_ext_op;
  alu_control_t id_alu_control;
  alu_a_sel_t id_alu_a_sel_d;
  alu_b_sel_t id_alu_b_sel_d;
  pc_alu_sel_t id_pc_alu_sel_d;
  result_sel_t id_result_sel_d;
  csr_bitmask_sel_t id_csr_bitmask_sel_d;


  //////////////////////////////////////
  //
  //
  //
  //
  // INSTRUCTION EXECUTE SIGNALS
  //
  //
  //
  //
  ///////////////////////////////////////

  logic [31:0] ex_pc_rdata_q;
  logic [31:0] ex_pc_wdata_d;
  logic [31:0] ex_pc_plus_4_q;
  logic [31:0] ex_insn_q;
  trap_info_t ex_trap_d;
  trap_info_t ex_carried_trap_q;
  logic [31:0] ex_rs1_rdata_q;
  logic [31:0] ex_rs1_rdata_d;
  logic [31:0] ex_rs2_rdata_q;
  logic [31:0] ex_rs2_rdata_d;
  logic [4:0] ex_rs1_addr_q;
  logic [4:0] ex_rs1_addr_d;
  logic [4:0] ex_rs2_addr_q;
  logic [4:0] ex_rs2_addr_d;
  logic [11:0] ex_csr_addr_q;
  logic [11:0] ex_csr_addr_d;
  logic [31:0] ex_csr_bitmask_comb;
  logic [31:0] ex_imm_ext_q;
  logic [2:0] ex_forward_a_sel_comb;
  logic [2:0] ex_forward_b_sel_comb;
  logic ex_pc_src_raw_comb;
  logic ex_pc_src_actual_comb;
  logic [31:0] ex_pc_target_actual_comb;
  logic [31:0] ex_src_a_tick_comb;
  logic [31:0] ex_src_a_comb;
  logic [31:0] ex_src_b_comb;
  logic [31:0] ex_pc_target_src_a_comb;
  logic ex_branch_cond_comb;
  logic ex_misaligned_jump_or_branch_comb;
  logic [31:0] ex_csr_rdata_q;
  logic [4:0] ex_rd_addr_q;
  logic [4:0] ex_rd_addr_d;
  logic [31:0] ex_store_wdata_raw_comb;
  logic ex_valid_q;
  logic ex_intr_q;
  logic [31:0] ex_alu_result_comb;
  logic ex_load_trap_valid;
  logic [30:0] ex_store_mcause;
  logic ex_store_trap_valid;
  logic [30:0] ex_load_trap_mcause;
  logic [31:0] ex_alu_csr_result_d;

  logic [31:0] ex_store_wdata_d;
  logic [3:0] ex_store_wmask_d;
  logic ex_load_is_signed_d;
  logic [3:0] ex_load_rmask_d;

  cpu_control_t ex_cpu_control_q;


  ///////////////////////////////////////
  //
  //
  //
  //
  // DATA MEMORY STAGE
  //
  //
  //
  //
  ///////////////////////////////////////

  logic [31:0] mem_pc_rdata_r;
  logic [31:0] mem_pc_plus_4_r;
  logic [31:0] mem_insn_r;
  trap_info_t mem_trap_d;
  trap_info_t mem_carried_trap_r;
  mem_op_t mem_mem_op_r;
  logic mem_misaligned_store;
  logic [31:0] mem_csr_rdata_r;
  logic [31:0] mem_csr_wdata_r;
  logic [31:0] mem_rs1_rdata_r;
  logic [31:0] mem_rs2_rdata_r;
  logic [4:0] mem_rs1_addr_r;
  logic [4:0] mem_rs2_addr_r;
  logic [11:0] mem_csr_addr_r;
  logic [1:0] mem_result_src_r;
  logic [3:0] mem_store_wmask_d;
  logic [3:0] mem_axil_rmask_r;
  logic [31:0] mem_alu_csr_result_r;
  logic [3:0] ex_dmem_wmask;
  logic [3:0] mem_dmem_wmask;
  logic [3:0] axil_wmask;
  logic [3:0] axil_rmask;
  logic [3:0] mem_load_rmask_d;
  logic [3:0] dmem_rmask;
  logic [3:0] ex_dmem_rmask;
  logic [31:0] mem_axil_rdata_r;
  logic [4:0] mem_rd_addr_r;
  logic [31:0] mem_load_rdata_d;
  logic [31:0] dmem_rdata_formatted;
  logic [31:0] mem_dmem_wdata_raw_r;
  logic [31:0] mem_dmem_wdata;
  logic mem_intr_r;
  logic mem_valid_insn_r;
  logic [31:0] axil_addr;
  logic mem_dmem_read_valid_raw_r;
  logic mem_axil_read_valid_raw_r;
  logic mem_dmem_read_valid_actual_comb;
  logic mem_axil_read_valid_actual_comb;
  logic dmem_actual_en;
  logic axil_actual_en;
  logic dmem_raw_en;
  logic axil_raw_en;

  logic [31:0] mem_store_wdata_d;
  logic [3:0] mem_store_wmask_r;
  logic mem_load_is_signed_r;
  logic [3:0] mem_load_rmask_r;

  cpu_control_t mem_cpu_control_r;

  ///////////////////////////////////////
  //
  //
  //
  //
  // WRITEBACK SIGNALS
  //
  //
  //
  //
  ///////////////////////////////////////
  logic [4:0] wb_rd_addr_masked;
  logic [31:0] wb_rd_wdata_masked;
  logic [31:0] wb_rd_wdata_comb;
  logic [31:0] wb_csr_rmask_comb;
  logic [31:0] wb_csr_wmask_comb;
  logic [31:0] ex_csr_wdata_d;
  trap_info_t wb_trap_d;
  cpu_control_t wb_cpu_control_r;




  // hazard unit signals
  // stops signals from propagating through the pipeline
  logic if_id_stall;
  logic id_ex_stall;
  logic ex_mem_stall;
  logic mem_wb_stall;

  // resets the pipeline to control signals of a NOP instruction
  logic if_id_flush;
  logic id_ex_flush;
  logic ex_mem_flush;
  logic mem_wb_flush;

  //////////////////////////////////////
  //
  //  INSTRUCTION FETCH STAGE
  //
  //
  ///////////////////////////////////////

  logic [31:0] pc_plus_4;
  logic [31:0] START_ADDR;
  assign START_ADDR = 32'd0;
  assign IMEM_EN = ~if_id_stall;

  // next pc logic
  always_comb begin
    unique case (ex_pc_src_actual_comb)
      // select pc incremented by 4
      1'b0: begin
        next_pc_comb = pc_plus_4;
      end
      // select pc from execute stage
      1'b1: begin
        next_pc_comb = ex_pc_target_actual_comb;
      end
      default: begin
        next_pc_comb = 0;
      end
    endcase
  end

  assign if_a_intr_comb = wb_trap_d.valid ? 1 : 0;
  assign if_a_pc_rdata_comb = wb_trap_d.valid ? trap_handler_addr_q : next_pc_comb;

  // pc incremented by 4
  assign pc_plus_4 = if_a_pc_rdata_r + 4;

  // register A 
  always_ff @(posedge CLK) begin
    if (RST) begin
      if_a_pc_rdata_r <= 0;
      if_a_intr_r <= 0;
      if_a_valid_insn_r <= 0;
    end else if (!if_id_stall) begin
      if_a_pc_rdata_r <= next_pc_comb;
      if_a_intr_r <= 0;
      if_a_valid_insn_r <= 1;
    end
  end
  // register B
  always_ff @(posedge CLK) begin
    if (RST) begin
      if_b_pc_rdata_r <= START_ADDR;
      if_b_pc_plus_4_r <= START_ADDR + 4;
      if_b_intr_r <= 0;
      if_b_valid_insn_r <= 1;
    end else if (!if_id_stall) begin
      if_b_pc_rdata_r <= if_a_pc_rdata_r;
      if_b_pc_plus_4_r <= pc_plus_4;
      if_b_intr_r <= if_a_intr_r;
      if_b_valid_insn_r <= if_a_valid_insn_r;
    end
  end



  //////////////////////////////////////
  //
  //  INSTRUCTION DECODE STAGE
  //
  //
  ///////////////////////////////////////
  assign id_op_comb = id_pipeline.insn[6:0];
  assign id_funct3_comb = id_pipeline.insn[14:12];
  assign id_funct7b5_comb = id_pipeline.insn[30];
  assign id_funct7_comb = id_pipeline.insn[31:25];
  assign id_funct12_comb = id_pipeline.insn[31:20];

  assign id_rtype_alt_comb = id_op_comb[5] & id_funct7b5_comb;
  assign id_itype_alt_comb = ~id_op_comb[5] & id_funct7b5_comb;
  assign id_rs1_addr_d = (id_cpu_control_comb.rs1_valid) ? id_pipeline.insn[19:15] : 0;
  assign id_rs2_addr_d = (id_cpu_control_comb.rs2_valid) ? id_pipeline.insn[24:20] : 0;
  assign id_rd_addr_d = (id_cpu_control_comb.rd_valid) ? id_pipeline.insn[11:7] : 0;
  assign id_csr_addr_d = (id_pipeline.valid) ? id_pipeline.insn[31:20] : 0;

  // select forwarded rs1 or rs2 rdata if needed
  assign id_rs1_rdata_d = id_forward_a_comb ? wb_rd_wdata_masked : id_rs1_rfile_rdata_comb;
  assign id_rs2_rdata_d = id_forward_b_comb ? wb_rd_wdata_masked : id_rs2_rfile_rdata_comb;

  decoder decoder_inst (
      .OP(id_op_comb),
      .FUNCT3(id_funct3_comb),
      .FUNCT7(id_funct7_comb),
      .FUNCT12(id_funct12_comb),
      .RS1_ADDR(id_rs1_addr_d),
      .RD_ADDR(id_rd_addr_d),
      .RTYPE_ALT(id_rtype_alt_comb),
      .ITYPE_ALT(id_itype_alt_comb),
      .RD_VALID(id_rd_valid_comb),
      .RS1_VALID(id_rs1_valid_comb),
      .RS2_VALID(id_rs2_valid_comb),
      .MEM_OP(id_mem_op_d),
      .CF_OP(id_cf_op_d),
      .CSR_OP(id_csr_op_d),
      .ALU_CONTROL(id_alu_control_d),
      .IMM_EXT_OP(id_imm_ext_op),
      .ALU_A_SRC(id_alu_a_sel_d),
      .ALU_B_SRC(id_alu_b_sel_d),
      .PC_ALU_SRC(id_pc_alu_sel_d),
      .RESULT_SRC(id_result_sel_d),
      .CSR_BITMASK_SEL(id_csr_bitmask_sel_d),
      .TRAP_MCAUSE(id_maindec_mcause_comb),
      .TRAP_VALID(id_maindec_trap_valid_comb)

  );

  extend extend_inst (
      .insn_i(id_pipeline.insn),
      .IMM_EXT_OP(id_imm_ext_op),
      .IMM_EXT(id_imm_ext_d)
  );

  // register file
  regfile regfile_inst (
      .clk_i(CLK),
      .rst_i(RST),
      .rs1_addr_i(id_rs1_addr_d),
      .rs2_addr_i(id_rs2_addr_d),
      .rd_addr_i(wb_rd_addr_masked),
      .reg_wr_data_i(wb_rd_wdata_masked),
      .rs1_rdata_o(id_rs1_rfile_rdata_comb),
      .rs2_rdata_o(id_rs2_rfile_rdata_comb)
  );


  csrfile csrfile_inst (
      .CLK(CLK),
      .RST(RST),
      .WB_RD_ADDR(wb_rd_addr_masked),
      .CSR_RADDR(id_csr_addr_d),
      .CSR_WADDR(wb_csr_addr_masked),
      .CSR_WDATA(wb_pipeline.csr_wdata),
      .WB_VALID_INSN(wb_pipeline.valid),
      .WB_TRAP(wb_trap_d),
      .TRAP_HANDLER_ADDR(trap_handler_addr_q),
      .CSR_RDATA_REG(ex_csr_rdata_q),
      .CSR_RMASK(wb_csr_rmask_comb),
      .CSR_WMASK(wb_csr_wmask_comb)
  );

  //////////////////////////////////////
  //
  //
  //
  //
  // INSTRUCTION EXECUTE STAGE
  //
  //
  //
  //
  ///////////////////////////////////////
  logic [31:0] ex_pc_target_raw_comb;

  assign ex_rs1_rdata_d = ex_src_a_tick_comb;
  assign ex_rs2_rdata_d = ex_store_wdata_raw_comb;
  assign ex_pc_src_raw_comb = (ex_cpu_control_q.cf_op[0] | (ex_cpu_control_q.cf_op[1] & ex_branch_cond_comb));

  assign ex_pc_wdata_d = (ex_pc_src_actual_comb) ? ex_pc_target_actual_comb : ex_pc_plus_4_q;
  // trap if a jump or branch address is misaligned
  //assign ex_misaligned_jump_or_branch_comb = ex_pc_src_actual_comb & (next_pc_comb[1] | next_pc_comb[0]);
  assign ex_misaligned_jump_or_branch_comb = ex_pc_src_actual_comb & (next_pc_comb[1] | next_pc_comb[0]);

  assign ex_pc_target_raw_comb = ex_pc_target_src_a_comb + ex_imm_ext_q;
  assign ex_pc_target_actual_comb     = (ex_cpu_control_q.cf_op == CF_JALR) ? (ex_pc_target_raw_comb & ~(1)) : ex_pc_target_raw_comb;

  // disable ex stage if trap propagates from previous stage
  // disable jumps, and set all register addresses to zero
  assign ex_rs1_addr_d = ex_carried_trap_q.valid ? 0 : ex_rs1_addr_q;
  assign ex_rs2_addr_d = ex_carried_trap_q.valid ? 0 : ex_rs2_addr_q;
  assign ex_rd_addr_d = ex_carried_trap_q.valid ? 0 : ex_rd_addr_q;
  assign ex_csr_addr_d = ex_carried_trap_q.valid ? 0 : ex_csr_addr_q;
  assign ex_pc_src_actual_comb = ex_carried_trap_q.valid ? 0 : ex_pc_src_raw_comb;
  // alu input 1 data path
  // select reg 1 data or data forwarded from WB or MEM stage
  always_comb begin
    case (ex_forward_a_sel_comb)
      NO_FORWARD_SEL:             ex_src_a_tick_comb = ex_rs1_rdata_q;
      FORWARD_SEL_MEM_ALU_RESULT: ex_src_a_tick_comb = mem_alu_csr_result_r;
      FORWARD_SEL_MEM_LOAD_RDATA: ex_src_a_tick_comb = mem_load_rdata_d;
      FORWARD_SEL_WB_RESULT:      ex_src_a_tick_comb = wb_rd_wdata_masked;
      default:                    ex_src_a_tick_comb = 0;
    endcase
  end
  // select data from first mux, zero, or pc
  always_comb begin
    case (ex_cpu_control_q.alu_a_src)
      ALU_A_SEL_REG_DATA: ex_src_a_comb = ex_src_a_tick_comb;
      ALU_A_SEL_ZERO:     ex_src_a_comb = 0;
      ALU_A_SEL_PC:       ex_src_a_comb = ex_pc_rdata_q;
      default:            ex_src_a_comb = 0;
    endcase
  end
  // alu input 2 data path
  // select reg 2 data or data forwarded from WB or MEM stage
  always_comb begin
    case (ex_forward_b_sel_comb)
      NO_FORWARD_SEL:             ex_store_wdata_raw_comb = ex_rs2_rdata_q;
      FORWARD_SEL_MEM_ALU_RESULT: ex_store_wdata_raw_comb = mem_alu_csr_result_r;
      FORWARD_SEL_MEM_LOAD_RDATA: ex_store_wdata_raw_comb = mem_load_rdata_d;
      FORWARD_SEL_WB_RESULT:      ex_store_wdata_raw_comb = wb_rd_wdata_masked;
      default:                    ex_store_wdata_raw_comb = 0;
    endcase
  end
  // select data from first mux, or extended immediate
  always_comb begin
    unique case (ex_cpu_control_q.alu_b_src)
      ALU_B_SEL_REG_DATA: ex_src_b_comb = ex_store_wdata_raw_comb;
      ALU_B_SEL_IMM:      ex_src_b_comb = ex_imm_ext_q;
    endcase
  end
  // select base address for branch/jump address, selecting either
  // the current pc or reg1_data.
  always_comb begin
    unique case (ex_cpu_control_q.pc_alu_src)
      PC_ALU_SEL_PC:          ex_pc_target_src_a_comb = ex_pc_rdata_q;
      PC_ALU_SELECT_REG_DATA: ex_pc_target_src_a_comb = ex_src_a_tick_comb;
    endcase
  end
  // select write value to be used in a csr instruction
  always_comb begin
    unique case (ex_cpu_control_q.csr_bitmask_sel)
      CSR_BITMASK_SEL_REG_DATA: ex_csr_bitmask_comb = ex_src_a_tick_comb;
      CSR_BITMASK_SEL_IMM:      ex_csr_bitmask_comb = ex_imm_ext_q;
    endcase
  end

  always_comb begin
    ex_csr_wdata_d = 0;
    case (ex_cpu_control_q.csr_op)
      CSR_WRITE: ex_csr_wdata_d = ex_csr_bitmask_comb;
      CSR_CLEAR: ex_csr_wdata_d = (ex_csr_rdata_q & ~ex_csr_bitmask_comb);
      CSR_SET:   ex_csr_wdata_d = (ex_csr_rdata_q | ex_csr_bitmask_comb);
      default:   ;
    endcase
  end


  assign ex_alu_csr_result_d = (ex_cpu_control_q.csr_op != CSR_NONE) ? ex_csr_rdata_q : ex_alu_result_comb;

  alu alu_inst (
      .a_i(ex_src_a_comb),
      .b_i(ex_src_b_comb),
      .control_i(ex_cpu_control_q.alu_control),
      .branch_cond_o(ex_branch_cond_comb),
      .result_o(ex_alu_result_comb)
  );

  // format store data for MEM stage
  store_unit store_unit_inst (
      .MEM_OP(ex_mem_op_r),
      .ADDR_LSB2(ex_alu_csr_result_d[1:0]),
      .STORE_WDATA_UNFORMATTED(ex_store_wdata_raw_comb),
      .STORE_TRAP_VALID(ex_store_trap_valid),
      .STORE_TRAP_MCAUSE(ex_store_mcause),
      .STORE_WMASK(ex_store_wmask_d),
      .STORE_WDATA(ex_store_wdata_d)
  );


  load_unit load_unit_inst (
      .MEM_OP(ex_cpu_control_q.mem_op),
      .ADDR_LSB2(ex_alu_csr_result_d[1:0]),
      .LOAD_TRAP_VALID(ex_load_trap_valid),
      .LOAD_TRAP_MCAUSE(ex_load_trap_mcause),
      .LOAD_RMASK(ex_load_rmask_d),
      .LOAD_IS_SIGNED(ex_load_is_signed_d)
  );

  ///////////////////////////////////////
  //
  //
  //
  //
  // DATA MEMORY STAGE
  //
  //
  //
  //
  ///////////////////////////////////////

  always_ff @(posedge CLK) begin
    if (RST) begin
      mem_axil_rdata_r <= 0;
      mem_dmem_read_valid_raw_r <= 0;
      mem_axil_read_valid_raw_r <= 0;
      mem_axil_rmask_r <= 0;
    end else begin
      mem_axil_rdata_r <= AXIL_TRANSACTION_RDATA;
      mem_dmem_read_valid_raw_r <= dmem_actual_en;
      mem_axil_read_valid_raw_r <= AXIL_DONE_READ;
      mem_axil_rmask_r <= axil_rmask;
    end
  end

  mem_router mem_router_inst (
      .MEM_ALU_RESULT(mem_alu_csr_result_r),
      .MEM_OP(mem_mem_op_r),
      .DMEM_EN(dmem_raw_en),
      .AXIL_EN(axil_raw_en),
      .AXIL_ADDR(axil_addr)
  );

  axil_interface #(
      .BUS_WIDTH(AXIL_BUS_WIDTH)
  ) axil_interface_inst (
      .CLK(CLK),
      .RST(RST),
      .EN(axil_actual_en),
      .MEM1_ALU_RESULT(mem_alu_csr_result_r),
      .MEM_OP(mem_mem_op_r),
      .MEM_WDATA_RAW(mem_store_wdata_d),
      .AXIL_ADDR(axil_addr),
      .AXIL_DONE_READ(AXIL_DONE_READ),
      .AXIL_DONE_WRITE(AXIL_DONE_WRITE),
      .AXIL_TRANSACTION_RDATA(AXIL_TRANSACTION_RDATA),
      .AXIL_START_READ(AXIL_START_READ),
      .AXIL_START_WRITE(AXIL_START_WRITE),
      .AXIL_TRANSACTION_WRADDR(AXIL_TRANSACTION_WRADDR),
      .AXIL_TRANSACTION_WRDATA(AXIL_TRANSACTION_WRDATA),
      .AXIL_TRANSACTION_WSTRB(AXIL_TRANSACTION_WSTRB),
      .AXIL_TRANSACTION_RADDR(AXIL_TRANSACTION_RADDR)
  );

  // disable dmem if address maps to axil peripheral
  logic [31:0] mem_actual_store_wdata_comb;
  logic [31:0] mem_actual_store_wmask_comb;
  logic [31:0] mem_actual_load_rdata_comb;
  logic [31:0] mem_actual_load_rmask_comb;

  // select dmem write data OR axil write data OR neither
  always_comb begin
    mem_actual_store_wdata_comb = 0;
    mem_actual_store_wmask_comb = 0;
    if (dmem_actual_en) begin
      mem_actual_store_wdata_comb = mem_dmem_wdata;
      mem_actual_store_wmask_comb = mem_dmem_wmask;
    end else if (axil_actual_en) begin
      mem_actual_store_wdata_comb = AXIL_TRANSACTION_WRDATA;
      mem_actual_store_wmask_comb = 4'hf;
    end
  end

  // select dmem read data OR axil read data OR neither
  always_comb begin
    mem_actual_load_rdata_comb = 0;
    mem_actual_load_rmask_comb = 0;
    if (mem_axil_read_valid_actual_comb) begin
      mem_actual_load_rdata_comb = AXIL_TRANSACTION_RDATA;
      mem_actual_load_rmask_comb = 4'hf;
    end else if (mem_dmem_read_valid_actual_comb) begin
      mem_actual_load_rdata_comb = dmem_rdata_formatted;
      mem_actual_load_rmask_comb = dmem_rmask;
    end
  end

  assign axil_rmask = 4'hf;
  assign dmem_actual_en = mem_carried_trap_r.valid ? 0 : dmem_raw_en;
  assign axil_actual_en = mem_carried_trap_r.valid ? 0 : axil_raw_en;
  assign DMEM_EN = dmem_actual_en;

  assign mem_axil_read_valid_actual_comb = mem_carried_trap_r.valid ? 0 : mem_axil_read_valid_raw_r;
  assign mem_dmem_read_valid_actual_comb = mem_carried_trap_r.valid ? 0 : mem_dmem_read_valid_raw_r;


  //////////////////////////////////////
  //
  //  WRITEBACK STAGE
  //
  //
  ///////////////////////////////////////
  // trap disable logic
  assign wb_rd_addr_masked = wb_pipeline.carried_trap.valid ? 0 : wb_pipeline.rd_addr;
  assign wb_csr_addr_masked = wb_pipeline.carried_trap.valid ? 0 : wb_pipeline.csr_addr;

  // disable register and csr writes for an excepted instruction
  // make sure that instructions that dont write to any register address have x0 as rd and 0 as rd_wdata
  assign wb_rd_wdata_masked = (wb_rd_addr_masked != 0) ? wb_rd_wdata_comb : 0;
  always_comb begin
    unique case (wb_pipeline.result_sel)
      2'b00: wb_rd_wdata_comb = wb_pipeline.alu_csr_result;
      2'b01: wb_rd_wdata_comb = wb_pipeline.load_rdata;
      2'b10: wb_rd_wdata_comb = wb_pipeline.pc_plus_4;
      2'b11: wb_rd_wdata_comb = wb_pipeline.csr_rdata;
    endcase
  end

  //////////////////////////////////////
  //
  //  PIPELINE REGISTERS
  //
  //
  ///////////////////////////////////////

  pipeline_t if_pipeline;
  pipeline_t id_pipeline;
  pipeline_t ex_pipeline;
  pipeline_t mem_pipeline;
  //IF/ID
  always_ff @(posedge CLK) begin
    if (RST) begin
      id_pipeline <= PIPELINE_T_RESET;
    end else if (!if_id_stall) begin
      id_pipeline <= '{
          pc: if_b_pc_rdata_r,
          pc_plus_4: if_b_pc_plus_4_r,
          insn: IMEM_RDATA,
          //rs1_addr: id_pipeline.rs1_addr,
          //rs2_addr: id_pipeline.rs2_addr,
          //rd_addr: id_pipeline.rd_addr,
          //rs1_data: id_pipeline.rs1_data,
          //rs2_data: id_pipeline.rs2_data,
          //imm_ext: id_pipeline.imm_ext,
          //csr_addr: id_pipeline.csr_addr,
          //csr_wdata: 0,
          //csr_rdata: 0,
          //csr_op: CSR_NONE,
          //cf_op: CF_NONE,
          //alu_control:id_pipeline.alu_control,
          //result_sel: RESULT_SEL_ALU_RESULT,
          //alu_a_sel: ALU_A_SEL_REG_DATA,
          //alu_b_sel: ALU_B_SEL_REG_DATA,
          //pc_alu_sel: PC_ALU_SEL_PC,
          //csr_bitmask_sel: CSR_BITMASK_SEL_REG_DATA,
          //mem_op: id_pipeline.mem_op,
          //load_is_signed: 0,
          //load_rmask: 0,
          //store_wdata: 0,
          //store_wmask: 0,
          //alu_csr_result: 0,
          //load_rdata: 0,
          //pc_wdata: 0,
          valid:
          if_b_valid_insn_r,
          intr: if_b_intr_r
      //carried_trap:
      };
    end
  end
  // ID/EX register
  always_ff @(posedge CLK) begin
    if (RST) begin
      ex_pipeline <= PIPELINE_T_RESET;
    end else if (!id_ex_stall) begin
      ex_pipeline <= '{
          pc: id_pipeline.pc,
          pc_plus_4: id_pipeline.pc_plus_4,
          insn: id_pipeline.insn,
          rs1_addr: id_rs1_addr_d,
          rs2_addr: id_rs2_addr_d,
          rd_addr: id_rd_addr_d,
          rs1_data: id_rs1_rdata_d,
          rs2_data: id_rs2_rdata_d,
          imm_ext: id_imm_ext_d,
          csr_addr: id_csr_addr_d,
          //csr_wdata: 0,
          //csr_rdata: 0,
          csr_op:
          id_csr_op_d,
          cf_op: id_cf_op_d,
          alu_control: id_alu_control_d,
          result_sel: id_result_sel_d,
          alu_a_sel: id_alu_a_sel_d,
          alu_b_sel: id_alu_b_sel_d,
          pc_alu_sel: id_pc_alu_sel_d,
          csr_bitmask_sel: id_csr_bitmask_sel_d,
          mem_op: id_mem_op_d,
          //load_is_signed: 0,
          //load_rmask: 0,
          //store_wdata: 0,
          //store_wmask: 0,
          //alu_csr_result: 0,
          //load_rdata: 0,
          //pc_wdata: 0,
          valid:
          id_pipeline.valid,
          intr: id_pipeline.intr,
          carried_trap: id_trap_d
      };
    end
  end
  // EX/MEM1 register
  always_ff @(posedge CLK) begin
    if (RST) begin
      mem_pipeline <= PIPELINE_T_RESET;
    end else if (!ex_mem_stall) begin
      mem_pipeline <= ex_pipeline <= '{
          pc: ex_pipeline.pc,
          pc_plus_4: ex_pipeline.pc_plus_4,
          insn: ex_pipeline.insn,
          rs1_addr: ex_rs1_addr_d,
          rs2_addr: ex_rs2_addr_d,
          rd_addr: ex_rd_addr_d,
          rs1_data: ex_rs1_rdata_d,
          rs2_data: ex_rs2_rdata_d,
          imm_ext: ex_pipeline.imm_ext,
          csr_addr: ex_csr_addr_d,
          csr_wdata: ex_csr_wdata_d,
          csr_rdata: ex_pipeline.csr_rdata,
          csr_op:
          ex_pipeline.csr_op,
          cf_op: ex_pipeline.cf_op,
          alu_control: ex_pipeline.alu_control,
          result_sel: ex_pipeline.result_sel,
          alu_a_sel: ex_pipeline.alu_a_sel,
          alu_b_sel: ex_pipeline.alu_b_sel,
          pc_alu_sel: ex_pipeline.pc_alu_sel,
          csr_bitmask_sel: ex_pipeline.csr_bitmask_sel,
          mem_op: ex_pipeline.mem_op,
          load_is_signed: ex_load_is_signed_d,
          load_rmask: ex_load_rmask_d,
          store_wdata: ex_store_wdata_d,
          store_wmask: ex_store_wmask_d,
          alu_csr_result: ex_alu_csr_result_d,
          //load_rdata: 0,
          pc_wdata:
          ex_pc_wdata_d,
          valid: ex_pipeline.valid,
          intr: ex_pipeline.intr,
          carried_trap: ex_trap_d
      };
    end
  end
  //MEM/WB
  always_ff @(posedge CLK) begin
    if (RST) begin
      wb_pipeline <= PIPELINE_T_RESET;
    end else if (!mem_wb_stall) begin
      wb_pipeline <= '{
          pc: wb_pipeline.pc,
          pc_plus_4: wb_pipeline.pc_plus_4,
          insn: wb_pipeline.insn,
          rs1_addr: mem_pipeline.rs1_addr,
          rs2_addr: mem_pipeline.rs2_addr,
          rd_addr: mem_pipeline.rd_addr,
          rs1_data: mem_pipeline.rs1_data,
          rs2_data: mem_pipeline.rs2_data,
          imm_ext: mem_pipeline.imm_ext,
          csr_addr: mem_pipeline.csr_addr,
          csr_wdata: mem_pipeline.csr_wdata,
          csr_rdata: mem_pipeline.csr_rdata,
          csr_op:
          mem_pipeline.csr_op,
          cf_op: mem_pipeline.cf_op,
          //alu_control: mem_pipeline.alu_control,
          result_sel:
          mem_pipeline.result_sel,
          //alu_a_sel: mem_pipeline.alu_a_sel,
          //alu_b_sel: mem_pipeline.alu_b_sel,
          //pc_alu_sel: mem_pipeline.pc_alu_sel,
          //csr_bitmask_sel: mem_pipeline.csr_bitmask_sel,
          mem_op:
          mem_pipeline.mem_op,
          load_is_signed: mem_load_is_signed_d,
          load_rmask: mem_load_rmask_d,
          store_wdata: mem_store_wdata_d,
          store_wmask: mem_store_wmask_d,
          alu_csr_result: mem_pipeline.alu_csr_result,
          load_rdata: mem_load_rdata_d,
          pc_wdata: mem_pipeline.pc_wdata,
          valid: mem_pipeline.valid,
          intr: mem_pipeline.intr,
          carried_trap: mem_trap_d
      };
    end
  end

  //////////////////////////////////////
  //
  //  TRAP HANDLING
  //
  //
  ///////////////////////////////////////
  // determine if the instruction generates a trap
  always_comb begin
    if (id_maindec_trap_valid_comb) begin
      id_trap_d = '{
          valid: 1,
          is_interrupt: 0,
          insn: id_pipeline.insn,
          mcause: id_maindec_mcause_comb,
          pc: id_pipeline.pc_rdata,
          next_pc: trap_handler_addr_q,
          rs1_addr: 0,
          rs2_addr: 0,
          rd_addr: 0,
          rs1_rdata: 0,
          rs2_rdata: 0,
          rd_wdata: 0
      };
    end else begin
      id_trap_d = '{default: 0};
    end
  end

  always_comb begin
    ex_trap_d = '{default: 0};
    /*
    if (ex_carried_trap_q.valid) begin
      ex_trap_d = ex_carried_trap_q;
    end else if (ex_misaligned_jump_or_branch_comb) begin
      ex_trap_d = '{
          valid: 1,
          is_interrupt: 0,
          insn: ex_insn_q,
          mcause: TRAP_CODE_INSTR_ADDR_MISALIGNED,
          pc: ex_pc_rdata_q,
          next_pc: trap_handler_addr_q,
          rs1_addr: ex_rs1_addr_q,
          rs2_addr: ex_rs2_addr_q,
          rd_addr: ex_rd_addr_q,
          rs1_rdata: ex_rs1_rdata_d,
          rs2_rdata: ex_rs2_rdata_d,
          rd_wdata: 0
      };
    end else begin
      ex_trap_d = '{default: 0};
    end
      */
  end

  always_comb begin
    mem_trap_d = '{default: 0};
    /*
    if (mem_carried_trap_r.valid) begin
      mem_trap_d = mem_carried_trap_r;
    end else if (ex_store_trap_valid) begin
      mem_trap_d = '{
          valid: 1,
          is_interrupt: 0,
          insn: mem_insn_r,
          mcause: ex_store_mcause,
          pc: mem_pc_rdata_r,
          next_pc: trap_handler_addr_q,
          rs1_addr: mem_rs1_addr_r,
          rs2_addr: mem_rs2_addr_r,
          rd_addr: mem_rd_addr_r,
          rs1_rdata: mem_rs1_rdata_r,
          rs2_rdata: mem_rs2_rdata_r,
          rd_wdata: 0
      };
    end else if (ex_load_trap_valid) begin
      mem_trap_d = '{
          valid: 1,
          is_interrupt: 0,
          insn: mem_insn_r,
          mcause: ex_load_trap_mcause,
          pc: mem_pc_rdata_r,
          next_pc: trap_handler_addr_q,
          rs1_addr: mem_rs1_addr_r,
          rs2_addr: mem_rs2_addr_r,
          rd_addr: mem_rd_addr_r,
          rs1_rdata: mem_rs1_rdata_r,
          rs2_rdata: mem_rs2_rdata_r,
          rd_wdata: 0
      };
    end else begin
      mem_trap_d = '{default: 0};
    end
    */
  end

  assign wb_trap_d = wb_carried_trap_r.valid ? wb_carried_trap_r : '{default: 0};

  //////////////////////////////////////
  //
  //  HAZARD LOGIC
  //
  //
  ///////////////////////////////////////

  hazard_unit hazard_unit_inst (
      .EX_RS1_ADDR(ex_rs1_addr_d),
      .EX_RS2_ADDR(ex_rs2_addr_d),
      .MEM_RD_ADDR(mem_rd_addr_r),
      .WB_RD_ADDR(wb_rd_addr_masked),
      .EX_RESULT_SRC(ex_result_src_r),
      .MEM_RESULT_SRC(mem_result_src_r),
      .ID_RS1_ADDR(id_rs1_addr_d),
      .ID_RS2_ADDR(id_rs2_addr_d),
      .EX_RD_ADDR(ex_rd_addr_d),
      .EX_PC_SRC(ex_pc_src_actual_comb),
      .EX_FORWARD_A(ex_forward_a_sel_comb),
      .EX_FORWARD_B(ex_forward_b_sel_comb),
      .ID_FORWARD_A(id_forward_a_comb),
      .ID_FORWARD_B(id_forward_b_comb),
      .IF_ID_FLUSH(if_id_flush),
      .ID_EX_FLUSH(id_ex_flush),
      .EX_MEM_FLUSH(ex_mem_flush),
      .MEM_WB_FLUSH(mem_wb_flush),
      .IF_ID_STALL(if_id_stall),
      .ID_EX_STALL(id_ex_stall),
      .EX_MEM_STALL(ex_mem_stall),
      .MEM_WB_STALL(mem_wb_stall),
      .EX_TRAP_VALID(ex_carried_trap_q.valid),
      .MEM_TRAP_VALID(mem_carried_trap_r.valid),
      .WB_TRAP_VALID(wb_carried_trap_r.valid),
      .AXIL_EN(axil_actual_en),
      .AXIL_DONE_READ(AXIL_DONE_READ),
      .AXIL_DONE_WRITE(AXIL_DONE_WRITE)
  );

  assign DMEM_ADDR  = mem_alu_csr_result_r[DMEM_ADDR_WIDTH-1:0];
  assign IMEM_ADDR  = if_a_pc_rdata_r[IMEM_ADDR_WIDTH-1:0];
  assign DMEM_WDATA = mem_store_wdata_d;
  assign DMEM_WMASK = mem_store_wmask_d;

  //////////////////////////////////////
  //
  //  FORMAL VERIFICATION
  //
  //
  ///////////////////////////////////////

`ifdef RISCV_FORMAL


  logic is_csr_mstatus;
  logic is_csr_misa;
  logic is_csr_mie;
  logic is_csr_mtvec;
  logic is_csr_mscratch;
  logic is_csr_mepc;
  logic is_csr_mcause;
  logic is_csr_mtval;
  logic is_csr_mip;
  logic is_csr_mcycle;
  logic is_csr_mcycleh;
  logic is_csr_minstret;
  logic is_csr_minstreth;
  logic is_csr_mvendorid;
  logic is_csr_marchid;
  logic is_csr_mimpid;
  logic is_csr_mhartid;
  logic is_csr_mconfigptr;
  logic rvfi_valid_next;
  assign rvfi_valid_next = mem_wb_stall ? 0 : wb_pipeline.valid;

  always_comb begin
    is_csr_mstatus = 0;
    is_csr_misa = 0;
    is_csr_mie = 0;
    is_csr_mtvec = 0;
    is_csr_mscratch = 0;
    is_csr_mepc = 0;
    is_csr_mcause = 0;
    is_csr_mtval = 0;
    is_csr_mip = 0;
    is_csr_mcycle = 0;
    is_csr_mcycleh = 0;
    is_csr_minstret = 0;
    is_csr_minstreth = 0;
    is_csr_mvendorid = 0;
    is_csr_marchid = 0;
    is_csr_mimpid = 0;
    is_csr_mhartid = 0;
    is_csr_mconfigptr = 0;
    case (wb_csr_addr_masked)
      12'h300: is_csr_mstatus = 1;
      12'h301: is_csr_misa = 1;
      12'h304: is_csr_mie = 1;
      12'h305: is_csr_mtvec = 1;
      12'h340: is_csr_mscratch = 1;
      12'h341: is_csr_mepc = 1;
      12'h342: is_csr_mcause = 1;
      12'h343: is_csr_mtval = 1;
      12'h344: is_csr_mip = 1;
      12'hB00: is_csr_mcycle = 1;
      12'hb80: is_csr_mcycleh = 1;
      12'hB02: is_csr_minstret = 1;
      12'hb82: is_csr_minstreth = 1;
      12'hf11: is_csr_mvendorid = 1;
      12'hf12: is_csr_marchid = 1;
      12'hf13: is_csr_mimpid = 1;
      12'hf14: is_csr_mhartid = 1;
      12'hf15: is_csr_mconfigptr = 1;
      default: ;
    endcase
  end

  always_ff @(posedge CLK) begin
    if (RST) begin
      rvfi_valid <= 0;
      rvfi_order <= 0;
      rvfi_insn <= 0;
      rvfi_trap <= 0;
      rvfi_halt <= 0;
      rvfi_intr <= 0;
      rvfi_mode <= 3;
      rvfi_ixl <= 1;

      rvfi_rs1_addr <= 0;
      rvfi_rs2_addr <= 0;
      rvfi_rs1_rdata <= 0;
      rvfi_rs2_rdata <= 0;

      rvfi_rd_addr <= 0;
      rvfi_rd_wdata <= 0;

      rvfi_pc_rdata <= 0;
      rvfi_pc_wdata <= 0;

      rvfi_mem_addr <= 0;
      rvfi_mem_rmask <= 0;
      rvfi_mem_wmask <= 0;
      rvfi_mem_rdata <= 0;
      rvfi_mem_wdata <= 0;

      rvfi_csr_mcycle_rmask <= 0;
      rvfi_csr_mcycle_wmask <= 0;
      rvfi_csr_mcycle_rdata <= 0;
      rvfi_csr_mcycle_wdata <= 0;

      rvfi_csr_minstret_rmask <= 0;
      rvfi_csr_minstret_wmask <= 0;
      rvfi_csr_minstret_rdata <= 0;
      rvfi_csr_minstret_wdata <= 0;

      rvfi_csr_mcause_rmask <= 0;
      rvfi_csr_mcause_wmask <= 0;
      rvfi_csr_mcause_rdata <= 0;
      rvfi_csr_mcause_wdata <= 0;

      rvfi_csr_mtvec_rmask <= 0;
      rvfi_csr_mtvec_wmask <= 0;
      rvfi_csr_mtvec_rdata <= 0;
      rvfi_csr_mtvec_wdata <= 0;

      rvfi_csr_mepc_rmask <= 0;
      rvfi_csr_mepc_wmask <= 0;
      rvfi_csr_mepc_rdata <= 0;
      rvfi_csr_mepc_wdata <= 0;
    end else begin
      rvfi_valid <= rvfi_valid_next;
      if (rvfi_valid_next) rvfi_order <= rvfi_order + 1;
      rvfi_mode <= 3;
      rvfi_ixl  <= 1;
      rvfi_halt <= 0;
      rvfi_trap <= wb_trap_d.valid;
      rvfi_intr <= wb_intr_r;

      if (wb_trap_d.valid) begin
        rvfi_insn <= wb_trap_d.insn;
        rvfi_rs1_addr <= wb_trap_d.rs1_addr;
        rvfi_rs2_addr <= wb_trap_d.rs2_addr;
        rvfi_rs1_rdata <= wb_trap_d.rs1_rdata;
        rvfi_rs2_rdata <= wb_trap_d.rs2_rdata;

        rvfi_rd_addr <= wb_trap_d.rd_addr;
        rvfi_rd_wdata <= wb_trap_d.rd_wdata;

        rvfi_pc_rdata <= wb_trap_d.pc;
        rvfi_pc_wdata <= wb_trap_d.next_pc;

        rvfi_mem_addr <= wb_alu_csr_result_r;
        rvfi_mem_rmask <= wb_load_rmask_r;
        rvfi_mem_wmask <= wb_store_wmask_r;
        rvfi_mem_rdata <= wb_load_rdata_r;
        rvfi_mem_wdata <= wb_store_wdata_r;
      end else begin
        rvfi_insn <= wb_pipeline.insn;
        rvfi_rs1_addr <= wb_rs1_addr_r;
        rvfi_rs2_addr <= wb_rs2_addr_r;
        rvfi_rs1_rdata <= wb_rs1_rdata_r;
        rvfi_rs2_rdata <= wb_rs2_rdata_r;

        rvfi_rd_addr <= wb_rd_addr_masked;
        rvfi_rd_wdata <= wb_rd_wdata_masked;

        rvfi_pc_rdata <= wb_pipeline.pc;
        rvfi_pc_wdata <= wb_trap_d.valid ? trap_handler_addr_q : wb_pipeline.pc_wdata;

        rvfi_mem_addr <= wb_alu_csr_result_r;
        rvfi_mem_rmask <= wb_load_rmask_r;
        rvfi_mem_wmask <= wb_store_wmask_r;
        rvfi_mem_rdata <= wb_load_rdata_r;
        rvfi_mem_wdata <= wb_store_wdata_r;
      end


      // make rmask and wmask cleared if an exception
      rvfi_csr_mcycle_wmask <= is_csr_mcycleh ? {wb_csr_wmask_comb, 32'd0} :
          is_csr_mcycle  ? {32'd0, wb_csr_wmask_comb} :
          64'd0;
      rvfi_csr_minstret_wmask <= is_csr_minstreth ? {wb_csr_wmask_comb, 32'd0} :
          is_csr_minstret  ? {32'd0, wb_csr_wmask_comb} :
          64'd0;
      rvfi_csr_mcause_wmask <= is_csr_mcause ? wb_csr_wmask_comb : 32'd0;
      rvfi_csr_mepc_wmask <= is_csr_mepc ? wb_csr_wmask_comb : 32'd0;
      rvfi_csr_mtvec_wmask <= is_csr_mtvec ? wb_csr_wmask_comb : 32'd0;
      // csr rmask logic
      rvfi_csr_mcycle_rmask <= is_csr_mcycleh ? {wb_csr_rmask_comb, 32'd0} :
          is_csr_mcycle  ? {32'd0, wb_csr_rmask_comb} :
          64'd0;
      rvfi_csr_minstret_rmask <= is_csr_minstreth ?  {wb_csr_rmask_comb, 32'd0} :
          is_csr_minstret  ? {32'd0, wb_csr_rmask_comb} :
          64'd0;
      rvfi_csr_mcause_rmask <= is_csr_mcause ? wb_csr_rmask_comb : 32'd0;
      rvfi_csr_mtvec_rmask <= is_csr_mtvec ? wb_csr_rmask_comb : 32'd0;
      rvfi_csr_mepc_rmask <= is_csr_mepc ? wb_csr_rmask_comb : 32'd0;

      rvfi_csr_mcycle_rdata <= is_csr_mcycleh ? {wb_csr_rdata_r, 32'd0} :
          is_csr_mcycle  ? {32'd0, wb_csr_rdata_r} :
          64'd0;
      rvfi_csr_minstret_rdata <= is_csr_minstreth ? {wb_csr_rdata_r, 32'd0} :
          is_csr_minstret  ? {32'd0, wb_csr_rdata_r} :
          64'd0;
      // csr rdata logic
      rvfi_csr_mcause_rdata <= is_csr_mcause ? wb_csr_rdata_r : 32'd0;
      rvfi_csr_mtvec_rdata <= is_csr_mtvec ? wb_csr_rdata_r : 32'd0;
      rvfi_csr_mepc_rdata <= is_csr_mepc ? wb_csr_rdata_r : 32'd0;

      rvfi_csr_mcycle_wdata <= is_csr_mcycleh ? {wb_pipeline.csr_wdata, 32'd0} :
          is_csr_mcycle  ? {32'd0, wb_pipeline.csr_wdata} :
          64'd0;
      rvfi_csr_minstret_wdata <= is_csr_minstreth ? {wb_pipeline.csr_wdata, 32'd0} :
          is_csr_minstret  ? {32'd0, wb_pipeline.csr_wdata} :
          64'd0;
      rvfi_csr_mcause_wdata <= is_csr_mcause ? wb_pipeline.csr_wdata : 32'd0;
      rvfi_csr_mtvec_wdata <= is_csr_mtvec ? wb_pipeline.csr_wdata : 32'd0;
      rvfi_csr_mepc_wdata <= is_csr_mepc ? wb_pipeline.csr_wdata : 32'd0;

    end
  end
`endif
endmodule
