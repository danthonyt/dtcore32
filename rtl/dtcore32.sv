
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

  logic [31:0] axil_addr;
  logic mem2_dmem_read_valid_raw_reg;
  logic mem2_axil_read_valid_raw_reg;
  logic mem2_dmem_read_valid_actual_comb;
  logic mem2_axil_read_valid_actual_comb;

  // IMEM AND DMEM SIGNALS
  logic [3:0] DMEM_mem_wmask;
  // hazard unit signals
  // stops signals from propagating through the pipeline
  logic if_id_stall;
  logic id_ex_stall;
  logic ex_mem1_stall;
  logic mem1_mem2_stall;
  logic mem2_wb_stall;

  // resets the pipeline to control signals of a NOP instruction
  logic if_id_flush;
  logic id_ex_flush;
  logic ex_mem1_flush;
  logic mem1_mem2_flush;
  logic mem2_wb_flush;

  logic [31:0] next_pc_comb;

  // instruction memory address of the instruction in the respective pipeline stage
  logic [31:0] if_a_pc_rdata_reg;
  logic [31:0] if_a_pc_rdata_comb;
  logic [31:0] id_pc_rdata_reg;
  logic [31:0] ex_pc_rdata_reg;
  logic [31:0] mem1_pc_rdata_reg;
  logic [31:0] mem2_pc_rdata_reg;
  logic [31:0] wb_pc_rdata_reg;

  // the pc of the next instruction
  logic [31:0] ex_pc_wdata_comb;
  logic [31:0] mem1_pc_wdata_reg;
  logic [31:0] mem2_pc_wdata_reg;
  logic [31:0] wb_pc_wdata_reg;

  logic [31:0] trap_handler_addr_reg;

  logic [31:0] if_b_pc_plus_4_reg;
  logic [31:0] id_pc_plus_4_reg;
  logic [31:0] ex_pc_plus_4_reg;
  logic [31:0] mem1_pc_plus_4_reg;
  logic [31:0] mem2_pc_plus_4_reg;
  logic [31:0] wb_pc_plus_4;

  logic [31:0] id_insn_reg;
  logic [31:0] ex_insn_reg;
  logic [31:0] mem1_insn_reg;
  logic [31:0] mem2_insn_reg;
  logic [31:0] wb_insn_reg;

  trap_info_t id_trap_comb;
  trap_info_t ex_trap_comb;
  trap_info_t mem1_trap_comb;
  trap_info_t mem2_trap_comb;
  trap_info_t wb_trap_comb;

  trap_info_t ex_carried_trap_reg;
  trap_info_t mem1_carried_trap_reg;
  trap_info_t mem2_carried_trap_reg;
  trap_info_t wb_carried_trap_reg;


  logic [2:0] id_mem_ltype_comb;
  logic [2:0] ex_mem_ltype_reg;
  logic [2:0] mem1_mem_ltype_reg;
  logic [2:0] mem2_mem_ltype_reg;

  logic id_jump_comb;
  logic ex_jump_reg;

  logic [31:0] id_rs1_rdata_comb;
  logic [31:0] id_rs1_regfile_rdata_comb;
  logic [31:0] ex_rs1_rdata_unforwarded_reg;
  logic [31:0] ex_rs1_rdata_comb;
  logic [31:0] mem1_rs1_rdata_reg;
  logic [31:0] mem2_rs1_rdata_reg;
  logic [31:0] wb_rs1_rdata_reg;

  logic [31:0] id_rs2_rdata_comb;
  logic [31:0] id_rs2_regfile_rdata_comb;
  logic [31:0] ex_rs2_rdata_unforwarded_reg;
  logic [31:0] ex_rs2_rdata_comb;
  logic [31:0] mem1_rs2_rdata_reg;
  logic [31:0] mem2_rs2_rdata_reg;
  logic [31:0] wb_rs2_rdata_reg;

  logic [4:0] id_rs1_addr_comb;
  logic [4:0] ex_rs1_addr_raw_reg;
  logic [4:0] ex_rs1_addr_actual_comb;
  logic [4:0] mem1_rs1_addr_reg;
  logic [4:0] mem2_rs1_addr_reg;
  logic [4:0] wb_rs1_addr_reg;

  logic [4:0] id_rs2_addr_comb;
  logic [4:0] ex_rs2_addr_raw_reg;
  logic [4:0] ex_rs2_addr_actual_comb;
  logic [4:0] mem1_rs2_addr_reg;
  logic [4:0] mem2_rs2_addr_reg;
  logic [4:0] wb_rs2_addr_reg;

  // actual csr being read/written
  logic [11:0] id_csr_addr_comb;
  logic [11:0] ex_csr_addr_raw_reg;
  logic [11:0] ex_csr_addr_actual_comb;
  logic [11:0] mem1_csr_addr_reg;
  logic [11:0] mem2_csr_addr_reg;
  logic [11:0] wb_csr_addr_raw_reg;
  logic [11:0] wb_csr_addr_actual_comb;

  // value used to write to a csr
  logic [31:0] ex_csr_bitmask_comb;

  // 00 = no csr write, 01 = direct write, 10 = clear bitmask, 11 = set bitmask
  logic [1:0] id_csr_wr_type_comb;
  logic [1:0] ex_csr_wr_type_reg;
  //logic [1:0] mem1_csr_wr_type_reg;
  //logic [1:0] mem2_csr_wr_type_reg;
  //logic [1:0] wb_csr_wr_type_reg;

  // 0 = register data value, 1 = immediate data value
  logic [1:0] id_result_src_comb;
  logic [1:0] ex_result_src_reg;
  logic [1:0] mem1_result_src_reg;
  logic [1:0] mem2_result_src_reg;
  logic [1:0] wb_result_src_reg;

  // 0 = register data value, 1 = immediate data value
  logic id_csr_bitmask_sel_comb;
  logic ex_csr_bitmask_sel_reg;

  // extended immediate value depending on the immediate type
  logic [31:0] id_imm_ext_comb;
  logic [31:0] ex_imm_ext_reg;

  // 00 = no write, 01 = word, 10 = half, 11 = byte
  logic [3:0] mem_wmask_comb;
  logic [3:0] dmem_wmask;
  logic [3:0] axil_wmask;
  logic [3:0] mem2_mem_wmask_reg;
  logic [3:0] wb_mem_wmask_reg;

  logic [3:0] mem_rmask_comb;
  logic [3:0] dmem_rmask;

  logic [3:0] axil_rmask;
  logic [3:0] mem2_axil_rmask_reg;
  logic [3:0] wb_mem_rmask_reg;

  logic [31:0] mem2_axil_rdata_reg;

  logic [1:0] id_mem_stype_comb;
  logic [1:0] ex_mem_stype_reg;
  logic [1:0] mem1_mem_stype_reg;

  // register destination for writes
  logic [4:0] id_rd_addr_comb;
  logic [4:0] ex_rd_addr_raw_reg;
  logic [4:0] ex_rd_addr_actual_comb;
  logic [4:0] mem1_rd_addr_reg;
  logic [4:0] mem2_rd_addr_reg;
  logic [4:0] wb_rd_addr_raw_reg;
  logic [4:0] wb_rd_addr_actual_comb;

  // result of alu operation depending on the instruction type
  logic [31:0] ex_alu_result_comb;
  logic [31:0] mem1_alu_csr_result_reg;
  logic [31:0] mem2_alu_csr_result_reg;
  logic [31:0] wb_alu_csr_result_reg;

  // 0 = pc, 1 = register source 1 data
  logic id_pc_target_alu_src_comb;
  logic ex_pc_target_alu_src_sel_reg;

  // read data from data memory
  logic [31:0] mem_rdata_comb;
  logic [31:0] dmem_rdata_formatted;
  logic [31:0] wb_mem_rdata_reg;

  logic id_is_jalr_comb;
  logic ex_is_jalr_reg;

  // o = not a branch instruction, 1 = is a branch instruction
  logic id_branch_comb;
  logic ex_branch_reg;

  logic [31:0] ex_mem_wdata_raw_comb;
  logic [31:0] mem1_mem_wdata_raw_reg;

  logic [3:0] id_alu_control_comb;
  logic [3:0] ex_alu_control_reg;

  logic id_alu_b_src_comb;
  logic ex_alu_b_src_sel_reg;

  logic [1:0] id_alu_a_src_comb;
  logic [1:0] ex_alu_a_src_sel_reg;

  logic [31:0] mem_wdata_comb;
  logic [31:0] dmem_wdata;
  logic [31:0] mem2_mem_wdata_reg;
  logic [31:0] wb_mem_wdata_reg;

  // 0 = not an actual instruction, or stalled.
  logic if_a_valid_insn_reg;
  logic if_a_valid_insn_comb;
  logic if_b_valid_insn_reg;
  logic id_valid_insn_reg;
  logic ex_valid_insn_reg;
  logic mem1_valid_insn_reg;
  logic mem2_valid_insn_reg;
  logic wb_valid_insn_reg;

  // used for rvfi interface
  logic if_a_intr_reg;
  logic if_a_intr_comb;
  logic if_b_intr_reg;
  logic id_intr_reg;
  logic ex_intr_reg;
  logic mem1_intr_reg;
  logic mem2_intr_reg;
  logic wb_intr_reg;

  // INSTRUCTION DECODE specific signals
  logic [2:0] id_imm_src_comb;
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
  logic id_valid_rs1_addr_comb;
  logic id_valid_rs2_addr_comb;
  logic id_valid_rd_addr_comb;
  logic [30:0] maindec_mcause_comb;
  logic maindec_trap_valid_comb;


  // EXECUTE stage specific signals
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

  // DATA MEMORY stage specific signals
  logic MEM_misaligned_store;

  // WRITEBACK stage specific signals
  logic [31:0] ex_csr_rdata_reg;
  logic [31:0] mem1_csr_rdata_reg;
  logic [31:0] mem2_csr_rdata_reg;
  logic [31:0] wb_csr_rdata_reg;
  logic [31:0] wb_result_comb;

  logic [31:0] wb_rd_wdata_comb;

  logic [31:0] wb_csr_rmask_comb;
  logic [31:0] wb_csr_wmask_comb;

  logic [31:0] ex_csr_wdata_comb;
  logic [31:0] mem1_csr_wdata_reg;
  logic [31:0] mem2_csr_wdata_reg;
  logic [31:0] wb_csr_wdata_reg;

  logic MEM2_load_trap_valid;
  logic [30:0] MEM2_load_trap_code;

  logic [30:0] MEM1_store_trap_code;
  logic mem1_store_trap_valid;

  //////////////////////////////////////
  //
  //  INSTRUCTION FETCH STAGE
  //
  //
  ///////////////////////////////////////
  logic [31:0] if_b_pc_rdata_reg;
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

  assign if_a_intr_comb = wb_trap_comb.valid ? 1 : 0;
  assign if_a_pc_rdata_comb = wb_trap_comb.valid ? trap_handler_addr_reg : next_pc_comb;

  // pc incremented by 4
  assign pc_plus_4 = if_a_pc_rdata_reg + 4;

  // register A 
  always_ff @(posedge CLK) begin
    if (RST) begin
      if_a_pc_rdata_reg <= 0;
      if_a_intr_reg <= 0;
      if_a_valid_insn_reg <= 0;
    end else if (wb_trap_comb.valid) begin  // jump to trap handler if retired instrucion has a trap
      if_a_pc_rdata_reg <= trap_handler_addr_reg;
      if_a_intr_reg <= 1;
      if_a_valid_insn_reg <= 1;
    end else if (!if_id_stall) begin
      if_a_pc_rdata_reg <= next_pc_comb;
      if_a_intr_reg <= 0;
      if_a_valid_insn_reg <= 1;
    end
  end
  // register B
  always_ff @(posedge CLK) begin
    if (RST) begin
      if_b_pc_rdata_reg <= START_ADDR;
      if_b_pc_plus_4_reg <= START_ADDR + 4;
      if_b_intr_reg <= 0;
      if_b_valid_insn_reg <= 1;
    end else if (if_id_flush) begin
      if_b_pc_rdata_reg <= 0;
      if_b_pc_plus_4_reg <= 0;
      if_b_intr_reg <= 0;
      if_b_valid_insn_reg <= 0;
    end else if (!if_id_stall) begin
      if_b_pc_rdata_reg <= if_a_pc_rdata_reg;
      if_b_pc_plus_4_reg <= pc_plus_4;
      if_b_intr_reg <= if_a_intr_reg;
      if_b_valid_insn_reg <= if_a_valid_insn_reg;
    end
  end



  //////////////////////////////////////
  //
  //  INSTRUCTION DECODE STAGE
  //
  //
  ///////////////////////////////////////
  assign id_op_comb = id_insn_reg[6:0];
  assign id_funct3_comb = id_insn_reg[14:12];
  assign id_funct7b5_comb = id_insn_reg[30];
  assign id_funct7_comb = id_insn_reg[31:25];
  assign id_funct12_comb = id_insn_reg[31:20];

  assign id_rtype_alt_comb = id_op_comb[5] & id_funct7b5_comb;
  assign id_itype_alt_comb = ~id_op_comb[5] & id_funct7b5_comb;
  assign id_rs1_addr_comb = (id_valid_rs1_addr_comb) ? id_insn_reg[19:15] : 0;
  assign id_rs2_addr_comb = (id_valid_rs2_addr_comb) ? id_insn_reg[24:20] : 0;
  assign id_rd_addr_comb = (id_valid_rd_addr_comb) ? id_insn_reg[11:7] : 0;
  assign id_csr_addr_comb = (id_valid_insn_reg) ? id_insn_reg[31:20] : 0;

  // select forwarded rs1 or rs2 rdata if needed
  assign id_rs1_rdata_comb = id_forward_a_comb ? wb_rd_wdata_comb : id_rs1_regfile_rdata_comb;
  assign id_rs2_rdata_comb = id_forward_b_comb ? wb_rd_wdata_comb : id_rs2_regfile_rdata_comb;


  maindec maindec_inst (
      .op_i(id_op_comb),
      .funct3_i(id_funct3_comb),
      .funct7_i(id_funct7_comb),
      .funct12_i(id_funct12_comb),
      .rs1_addr_i(id_rs1_addr_comb),
      .rd_addr_i(id_rd_addr_comb),
      .valid_rd_addr_o(id_valid_rd_addr_comb),
      .valid_rs1_addr_o(id_valid_rs1_addr_comb),
      .valid_rs2_addr_o(id_valid_rs2_addr_comb),
      .imm_src_o(id_imm_src_comb),
      .alu_a_src_o(id_alu_a_src_comb),
      .alu_b_src_o(id_alu_b_src_comb),
      .mem_stype_o(id_mem_stype_comb),
      .result_src_o(id_result_src_comb),
      .branch_o(id_branch_comb),
      .alu_op_o(id_alu_op_comb),
      .jump_o(id_jump_comb),
      .pc_target_alu_src_o(id_pc_target_alu_src_comb),
      .mem_ltype_o(id_mem_ltype_comb),
      .csr_wtype_o(id_csr_wr_type_comb),
      .csr_write_src_o(id_csr_bitmask_sel_comb),
      .is_jalr_o(id_is_jalr_comb),
      .trap_mcause_o(maindec_mcause_comb),
      .trap_valid_o(maindec_trap_valid_comb)
  );

  extend extend_inst (
      .insn_i(id_insn_reg),
      .imm_src_i(id_imm_src_comb),
      .imm_ext_o(id_imm_ext_comb)
  );
  aludec aludec_inst (
      .alu_op_i(id_alu_op_comb),
      .rtype_alt_i(id_rtype_alt_comb),
      .itype_alt_i(id_itype_alt_comb),
      .funct3_i(id_funct3_comb),
      .alu_control_o(id_alu_control_comb)
  );
  // register file
  regfile regfile_inst (
      .clk_i(CLK),
      .rst_i(RST),
      .rs1_addr_i(id_rs1_addr_comb),
      .rs2_addr_i(id_rs2_addr_comb),
      .rd_addr_i(wb_rd_addr_actual_comb),
      .reg_wr_data_i(wb_rd_wdata_comb),
      .rs1_rdata_o(id_rs1_regfile_rdata_comb),
      .rs2_rdata_o(id_rs2_regfile_rdata_comb)
  );


  csrfile csrfile_inst (
      .CLK(CLK),
      .RST(RST),
      .WB_RD_ADDR(wb_rd_addr_actual_comb),
      .CSR_RADDR(id_csr_addr_comb),
      .CSR_WADDR(wb_csr_addr_actual_comb),
      .CSR_WDATA(wb_csr_wdata_reg),
      .WB_VALID_INSN(wb_valid_insn_reg),
      .WB_TRAP(wb_trap_comb),
      .TRAP_HANDLER_ADDR(trap_handler_addr_reg),
      .CSR_RDATA_REG(ex_csr_rdata_reg),
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

  assign ex_rs1_rdata_comb = ex_src_a_tick_comb;
  assign ex_rs2_rdata_comb = ex_mem_wdata_raw_comb;
  assign ex_pc_src_raw_comb = (ex_jump_reg | (ex_branch_reg & ex_branch_cond_comb));

  assign ex_pc_wdata_comb = (ex_pc_src_actual_comb) ? ex_pc_target_actual_comb : ex_pc_plus_4_reg;
  // trap if a jump or branch address is misaligned
  //assign ex_misaligned_jump_or_branch_comb = ex_pc_src_actual_comb & (next_pc_comb[1] | next_pc_comb[0]);
  assign ex_misaligned_jump_or_branch_comb = ex_pc_src_actual_comb & (next_pc_comb[1] | next_pc_comb[0]);

  assign ex_pc_target_raw_comb = ex_pc_target_src_a_comb + ex_imm_ext_reg;
  assign ex_pc_target_actual_comb     = ex_is_jalr_reg ? (ex_pc_target_raw_comb & ~(1)) : ex_pc_target_raw_comb;

  // disable ex stage if trap propagates from previous stage
  // disable jumps, and set all register addresses to zero
  assign ex_rs1_addr_actual_comb = ex_carried_trap_reg.valid ? 0 : ex_rs1_addr_raw_reg;
  assign ex_rs2_addr_actual_comb = ex_carried_trap_reg.valid ? 0 : ex_rs2_addr_raw_reg;
  assign ex_rd_addr_actual_comb = ex_carried_trap_reg.valid ? 0 : ex_rd_addr_raw_reg;
  assign ex_csr_addr_actual_comb = ex_carried_trap_reg.valid ? 0 : ex_csr_addr_raw_reg;
  assign ex_pc_src_actual_comb = ex_carried_trap_reg.valid ? 0 : ex_pc_src_raw_comb;
  // alu input 1 data path
  // select reg 1 data or data forwarded from WB or MEM stage
  always_comb begin
    case (ex_forward_a_sel_comb)
      FORWARD_SEL_NO_FORWARD:      ex_src_a_tick_comb = ex_rs1_rdata_unforwarded_reg;
      FORWARD_SEL_MEM1_ALU_RESULT: ex_src_a_tick_comb = mem1_alu_csr_result_reg;
      FORWARD_SEL_MEM2_ALU_RESULT: ex_src_a_tick_comb = mem2_alu_csr_result_reg;
      FORWARD_SEL_MEM2_MEM_RDATA:  ex_src_a_tick_comb = mem_rdata_comb;
      FORWARD_SEL_WB_RESULT:       ex_src_a_tick_comb = wb_result_comb;
      default:                     ex_src_a_tick_comb = 0;
    endcase
  end
  // select data from first mux, zero, or pc
  always_comb begin
    case (ex_alu_a_src_sel_reg)
      ALU_A_SRC_SELECT_REG_DATA: ex_src_a_comb = ex_src_a_tick_comb;
      ALU_A_SRC_SELECT_ZERO:     ex_src_a_comb = 0;
      ALU_A_SRC_SELECT_PC:       ex_src_a_comb = ex_pc_rdata_reg;
      default:                   ex_src_a_comb = 0;
    endcase
  end
  // alu input 2 data path
  // select reg 2 data or data forwarded from WB or MEM stage
  always_comb begin
    case (ex_forward_b_sel_comb)
      FORWARD_SEL_NO_FORWARD:      ex_mem_wdata_raw_comb = ex_rs2_rdata_unforwarded_reg;
      FORWARD_SEL_MEM1_ALU_RESULT: ex_mem_wdata_raw_comb = mem1_alu_csr_result_reg;
      FORWARD_SEL_MEM2_ALU_RESULT: ex_mem_wdata_raw_comb = mem2_alu_csr_result_reg;
      FORWARD_SEL_MEM2_MEM_RDATA:  ex_mem_wdata_raw_comb = mem_rdata_comb;
      FORWARD_SEL_WB_RESULT:       ex_mem_wdata_raw_comb = wb_result_comb;
      default:                     ex_mem_wdata_raw_comb = 0;
    endcase
  end
  // select data from first mux, or extended immediate
  always_comb begin
    unique case (ex_alu_b_src_sel_reg)
      ALU_B_SRC_SELECT_REG_DATA: ex_src_b_comb = ex_mem_wdata_raw_comb;
      ALU_B_SRC_SELECT_IMM:      ex_src_b_comb = ex_imm_ext_reg;
    endcase
  end
  // select base address for branch/jump address, selecting either
  // the current pc or reg1_data.
  always_comb begin
    unique case (ex_pc_target_alu_src_sel_reg)
      PC_TARGET_ALU_SRC_SELECT_PC:       ex_pc_target_src_a_comb = ex_pc_rdata_reg;
      PC_TARGET_ALU_SRC_SELECT_REG_DATA: ex_pc_target_src_a_comb = ex_src_a_tick_comb;
    endcase
  end
  // select write value to be used in a csr instruction
  always_comb begin
    unique case (ex_csr_bitmask_sel_reg)
      CSR_SRC_SELECT_REG_DATA: ex_csr_bitmask_comb = ex_src_a_tick_comb;
      CSR_SRC_SELECT_IMM:      ex_csr_bitmask_comb = ex_imm_ext_reg;
    endcase
  end

  always_comb begin
    ex_csr_wdata_comb = 0;
    case (ex_csr_wr_type_reg)
      CSR_WRITE_RAW_VALUE:      ex_csr_wdata_comb = ex_csr_bitmask_comb;
      CSR_WRITE_CLEAR_BIT_MASK: ex_csr_wdata_comb = (ex_csr_rdata_reg & ~ex_csr_bitmask_comb);
      CSR_WRITE_SET_BIT_MASK:   ex_csr_wdata_comb = (ex_csr_rdata_reg | ex_csr_bitmask_comb);
      default:                  ;
    endcase
  end

  logic [31:0] ex_alu_csr_result_comb;
  assign ex_alu_csr_result_comb = (|ex_csr_wr_type_reg) ? ex_csr_rdata_reg : ex_alu_result_comb;

  alu alu_inst (
      .a_i(ex_src_a_comb),
      .b_i(ex_src_b_comb),
      .control_i(ex_alu_control_reg),
      .branch_cond_o(ex_branch_cond_comb),
      .result_o(ex_alu_result_comb)
  );


  //////////////////////////////////////
  //
  //  DATA MEMORY 1 STAGE
  //
  //
  ///////////////////////////////////////

  logic dmem_actual_en;
  logic axil_actual_en;
  logic dmem_raw_en;
  logic axil_raw_en;

  assign dmem_actual_en = mem1_carried_trap_reg.valid ? 0 : dmem_raw_en;
  assign axil_actual_en = mem1_carried_trap_reg.valid ? 0 : axil_raw_en;
  assign DMEM_EN = dmem_actual_en;

  // enables DMEM or AXIL
  mem_router #(
      .ADDR_WIDTH(32)
  ) mem_router_inst (
      .MEM1_ALU_RESULT(mem1_alu_csr_result_reg),
      .MEM1_MEM_LTYPE(mem1_mem_ltype_reg),
      .MEM1_MEM_STYPE(mem1_mem_stype_reg),
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
      .MEM1_ALU_RESULT(mem1_alu_csr_result_reg),
      .MEM1_MEM_LTYPE(mem1_mem_ltype_reg),
      .MEM1_MEM_STYPE(mem1_mem_stype_reg),
      .MEM1_WDATA_RAW(mem1_mem_wdata_raw_reg),
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
  assign axil_rmask = 4'hf;
  // disable dmem if address maps to axil peripheral

  store_unit store_unit_inst (
      .en(dmem_actual_en),
      .store_size_i(mem1_mem_stype_reg),
      .addr_lsb2_i(mem1_alu_csr_result_reg[1:0]),
      .wdata_unformatted_i(mem1_mem_wdata_raw_reg),
      .store_trap_o(mem1_store_trap_valid),
      .trap_code_o(MEM1_store_trap_code),
      .wmask_o(dmem_wmask),
      .wdata_formatted_o(dmem_wdata)
  );


  // select dmem write data OR axil write data OR neither
  always_comb begin
    mem_wdata_comb = 0;
    mem_wmask_comb = 0;
    if (dmem_actual_en) begin
      mem_wdata_comb = dmem_wdata;
      mem_wmask_comb = dmem_wmask;
    end else if (axil_actual_en) begin
      mem_wdata_comb = AXIL_TRANSACTION_WRDATA;
      mem_wmask_comb = 4'hf;
    end
  end


  //////////////////////////////////////
  //
  //  DATA MEMORY 2 STAGE
  //
  //
  ///////////////////////////////////////
  assign mem2_axil_read_valid_actual_comb = mem2_carried_trap_reg.valid ? 0 : mem2_axil_read_valid_raw_reg;
  assign mem2_dmem_read_valid_actual_comb = mem2_carried_trap_reg.valid ? 0 : mem2_dmem_read_valid_raw_reg;
  load_unit load_unit_inst (
      .en(mem2_dmem_read_valid_actual_comb),
      .load_type(mem2_mem_ltype_reg),
      .addr_lsb2(mem2_alu_csr_result_reg[1:0]),
      .rdata_unformatted_i(DMEM_RDATA),
      .load_trap_o(MEM2_load_trap_valid),
      .load_trap_code_o(MEM2_load_trap_code),
      .rmask_o(dmem_rmask),
      .rdata_formatted_o(dmem_rdata_formatted)
  );
  // select dmem read data OR axil read data OR neither
  always_comb begin
    mem_rdata_comb = 0;
    mem_rmask_comb = 0;
    if (mem2_axil_read_valid_actual_comb) begin
      mem_rdata_comb = mem2_axil_rdata_reg;
      mem_rmask_comb = 4'hf;
    end else if (mem2_dmem_read_valid_actual_comb) begin
      mem_rdata_comb = dmem_rdata_formatted;
      mem_rmask_comb = dmem_rmask;
    end
  end



  //////////////////////////////////////
  //
  //  WRITEBACK STAGE
  //
  //
  ///////////////////////////////////////
  // trap disable logic
  assign wb_rd_addr_actual_comb = wb_carried_trap_reg.valid ? 0 : wb_rd_addr_raw_reg;
  assign wb_csr_addr_actual_comb = wb_carried_trap_reg.valid ? 0 : wb_csr_addr_raw_reg;

  // disable register and csr writes for an excepted instruction
  // make sure that instructions that dont write to any register address have x0 as rd and 0 as rd_wdata
  assign wb_rd_wdata_comb = (wb_rd_addr_actual_comb != 0) ? wb_result_comb : 0;
  always_comb begin
    unique case (wb_result_src_reg)
      2'b00: wb_result_comb = wb_alu_csr_result_reg;
      2'b01: wb_result_comb = wb_mem_rdata_reg;
      2'b10: wb_result_comb = wb_pc_plus_4;
      2'b11: wb_result_comb = wb_csr_rdata_reg;
    endcase
  end

  //////////////////////////////////////
  //
  //  PIPELINE REGISTERS
  //
  //
  ///////////////////////////////////////

  //IF/ID
  always_ff @(posedge CLK) begin
    if (RST) begin
      id_insn_reg <= NOP_INSTRUCTION;
      id_pc_rdata_reg <= 0;
      id_pc_plus_4_reg <= 0;
      id_valid_insn_reg <= 0;
      id_intr_reg <= 0;
    end else if (if_id_flush) begin
      id_insn_reg <= NOP_INSTRUCTION;
      id_pc_rdata_reg <= 0;
      id_pc_plus_4_reg <= 0;
      id_valid_insn_reg <= 0;
      id_intr_reg <= 0;
    end else if (!if_id_stall) begin
      if (!if_b_valid_insn_reg) begin
        id_insn_reg <= NOP_INSTRUCTION;
        id_pc_rdata_reg <= 0;
        id_pc_plus_4_reg <= 0;
        id_valid_insn_reg <= 0;
        id_intr_reg <= 0;
      end else begin
        id_insn_reg <= IMEM_RDATA;
        id_pc_rdata_reg <= if_b_pc_rdata_reg;
        id_pc_plus_4_reg <= if_b_pc_plus_4_reg;
        id_valid_insn_reg <= if_b_valid_insn_reg;
        id_intr_reg <= if_b_intr_reg;
      end
    end
  end
  // ID/EX register
  always_ff @(posedge CLK) begin
    if (RST || id_ex_flush) begin
      ex_result_src_reg <= 0;
      ex_mem_ltype_reg <= 0;
      ex_mem_stype_reg <= 0;
      ex_jump_reg <= 0;
      ex_branch_reg <= 0;
      ex_alu_control_reg <= 0;
      ex_alu_a_src_sel_reg <= 0;
      ex_alu_b_src_sel_reg <= 0;
      ex_pc_target_alu_src_sel_reg <= 0;
      ex_rs1_rdata_unforwarded_reg <= 0;
      ex_rs2_rdata_unforwarded_reg <= 0;
      ex_pc_rdata_reg <= 0;
      ex_rs1_addr_raw_reg <= 0;
      ex_rs2_addr_raw_reg <= 0;
      ex_rd_addr_raw_reg <= 0;
      ex_imm_ext_reg <= 0;
      ex_pc_plus_4_reg <= 0;
      ex_insn_reg <= NOP_INSTRUCTION;
      ex_csr_addr_raw_reg <= 0;
      ex_csr_bitmask_sel_reg <= 0;
      ex_csr_wr_type_reg <= 0;
      ex_is_jalr_reg <= 0;
      ex_carried_trap_reg <= '{default: 0};
      ex_valid_insn_reg <= 0;
      ex_intr_reg <= 0;
    end else if (!id_ex_stall) begin
      ex_result_src_reg <= id_result_src_comb;
      ex_mem_ltype_reg <= id_mem_ltype_comb;
      ex_mem_stype_reg <= id_mem_stype_comb;
      ex_jump_reg <= id_jump_comb;
      ex_branch_reg <= id_branch_comb;
      ex_alu_control_reg <= id_alu_control_comb;
      ex_alu_a_src_sel_reg <= id_alu_a_src_comb;
      ex_alu_b_src_sel_reg <= id_alu_b_src_comb;
      ex_pc_target_alu_src_sel_reg <= id_pc_target_alu_src_comb;
      ex_rs1_rdata_unforwarded_reg <= id_rs1_rdata_comb;
      ex_rs2_rdata_unforwarded_reg <= id_rs2_rdata_comb;
      ex_pc_rdata_reg <= id_pc_rdata_reg;
      ex_rs1_addr_raw_reg <= id_rs1_addr_comb;
      ex_rs2_addr_raw_reg <= id_rs2_addr_comb;
      ex_rd_addr_raw_reg <= id_rd_addr_comb;
      ex_imm_ext_reg <= id_imm_ext_comb;
      ex_pc_plus_4_reg <= id_pc_plus_4_reg;
      ex_insn_reg <= id_insn_reg;
      ex_carried_trap_reg <= id_trap_comb;
      ex_csr_addr_raw_reg <= id_csr_addr_comb;
      ex_csr_bitmask_sel_reg <= id_csr_bitmask_sel_comb;
      ex_csr_wr_type_reg <= id_csr_wr_type_comb;
      ex_valid_insn_reg <= id_valid_insn_reg;
      ex_intr_reg <= id_intr_reg;
      ex_is_jalr_reg <= id_is_jalr_comb;
    end
  end
  // EX/MEM1 register
  always_ff @(posedge CLK) begin
    if (RST || ex_mem1_flush) begin
      mem1_result_src_reg <= 0;
      mem1_mem_ltype_reg <= 0;
      mem1_mem_stype_reg <= 0;
      mem1_alu_csr_result_reg <= 0;
      mem1_mem_wdata_raw_reg <= 0;
      mem1_rd_addr_reg <= 0;
      mem1_pc_rdata_reg <= 0;
      mem1_pc_plus_4_reg <= 0;
      mem1_insn_reg <= NOP_INSTRUCTION;
      mem1_csr_addr_reg <= 0;
      mem1_rs1_rdata_reg <= 0;
      mem1_rs2_rdata_reg <= 0;
      mem1_rs1_addr_reg <= 0;
      mem1_rs2_addr_reg <= 0;
      mem1_pc_wdata_reg <= 0;
      mem1_carried_trap_reg <= '{default: 0};
      mem1_valid_insn_reg <= 0;
      mem1_intr_reg <= 0;
      mem1_csr_wdata_reg <= 0;
      mem1_csr_rdata_reg <= 0;
    end else if (!ex_mem1_stall) begin
      mem1_result_src_reg <= ex_result_src_reg;
      mem1_mem_ltype_reg <= ex_mem_ltype_reg;
      mem1_mem_stype_reg <= ex_mem_stype_reg;
      mem1_alu_csr_result_reg <= ex_alu_csr_result_comb;
      mem1_mem_wdata_raw_reg <= ex_mem_wdata_raw_comb;
      mem1_rd_addr_reg <= ex_rd_addr_actual_comb;
      mem1_pc_rdata_reg <= ex_pc_rdata_reg;
      mem1_pc_plus_4_reg <= ex_pc_plus_4_reg;
      mem1_carried_trap_reg <= ex_trap_comb;
      mem1_insn_reg <= ex_insn_reg;
      mem1_csr_addr_reg <= ex_csr_addr_actual_comb;
      mem1_valid_insn_reg <= ex_valid_insn_reg;
      mem1_intr_reg <= ex_intr_reg;
      mem1_rs1_rdata_reg <= ex_rs1_rdata_comb;
      mem1_rs2_rdata_reg <= ex_rs2_rdata_comb;
      mem1_rs1_addr_reg <= ex_rs1_addr_actual_comb;
      mem1_rs2_addr_reg <= ex_rs2_addr_actual_comb;
      mem1_pc_wdata_reg <= ex_pc_wdata_comb;
      mem1_csr_wdata_reg <= ex_csr_wdata_comb;
      mem1_csr_rdata_reg <= ex_csr_rdata_reg;
    end
  end
  // MEM1/MEM2
  always_ff @(posedge CLK) begin
    if (RST || mem1_mem2_flush) begin
      mem2_result_src_reg <= 0;
      mem2_mem_ltype_reg <= 0;
      mem2_alu_csr_result_reg <= 0;
      mem2_rd_addr_reg <= 0;
      mem2_pc_rdata_reg <= 0;
      mem2_pc_plus_4_reg <= 0;
      mem2_insn_reg <= NOP_INSTRUCTION;
      mem2_csr_addr_reg <= 0;
      mem2_rs1_rdata_reg <= 0;
      mem2_rs2_rdata_reg <= 0;
      mem2_rs1_addr_reg <= 0;
      mem2_rs2_addr_reg <= 0;
      mem2_pc_wdata_reg <= 0;
      mem2_axil_rdata_reg <= 0;
      mem2_dmem_read_valid_raw_reg <= 0;
      mem2_axil_read_valid_raw_reg <= 0;
      mem2_axil_rmask_reg <= 0;
      mem2_carried_trap_reg <= '{default: 0};
      mem2_valid_insn_reg <= 0;
      mem2_intr_reg <= 0;
      mem2_csr_wdata_reg <= 0;
      mem2_csr_rdata_reg <= 0;
    end else if (!mem1_mem2_stall) begin
      mem2_result_src_reg <= mem1_result_src_reg;
      mem2_mem_ltype_reg <= mem1_mem_ltype_reg;
      mem2_alu_csr_result_reg <= mem1_alu_csr_result_reg;
      mem2_rd_addr_reg <= mem1_rd_addr_reg;
      mem2_pc_rdata_reg <= mem1_pc_rdata_reg;
      mem2_pc_plus_4_reg <= mem1_pc_plus_4_reg;
      mem2_carried_trap_reg <= mem1_trap_comb;
      mem2_insn_reg <= mem1_insn_reg;
      mem2_csr_addr_reg <= mem1_csr_addr_reg;
      mem2_valid_insn_reg <= mem1_valid_insn_reg;
      mem2_intr_reg <= mem1_intr_reg;
      mem2_rs1_rdata_reg <= mem1_rs1_rdata_reg;
      mem2_rs2_rdata_reg <= mem1_rs2_rdata_reg;
      mem2_rs1_addr_reg <= mem1_rs1_addr_reg;
      mem2_rs2_addr_reg <= mem1_rs2_addr_reg;
      mem2_pc_wdata_reg <= mem1_pc_wdata_reg;
      mem2_mem_wdata_reg <= mem_wdata_comb;
      mem2_mem_wmask_reg <= mem_wmask_comb;
      mem2_axil_rdata_reg <= AXIL_TRANSACTION_RDATA;
      mem2_dmem_read_valid_raw_reg <= dmem_actual_en;
      mem2_axil_read_valid_raw_reg <= AXIL_DONE_READ;
      mem2_axil_rmask_reg <= axil_rmask;
      mem2_csr_wdata_reg <= mem1_csr_wdata_reg;
      mem2_csr_rdata_reg <= mem1_csr_rdata_reg;
    end
  end
  //MEM2/WB
  always_ff @(posedge CLK) begin
    if (RST || mem2_wb_flush) begin
      wb_rd_addr_raw_reg <= 0;
      wb_insn_reg <= NOP_INSTRUCTION;
      wb_alu_csr_result_reg <= 0;
      wb_mem_rdata_reg <= 0;
      wb_pc_rdata_reg <= 0;
      wb_pc_plus_4 <= 0;
      wb_result_src_reg <= 0;
      wb_csr_addr_raw_reg <= 0;
      wb_rs1_rdata_reg <= 0;
      wb_rs2_rdata_reg <= 0;
      wb_rs1_addr_reg <= 0;
      wb_rs2_addr_reg <= 0;
      wb_mem_rdata_reg <= 0;
      wb_mem_rmask_reg <= 0;
      wb_mem_wdata_reg <= 0;
      wb_mem_wmask_reg <= 0;
      wb_pc_wdata_reg <= 0;
      wb_carried_trap_reg <= '{default: 0};
      wb_valid_insn_reg <= 0;
      wb_intr_reg <= 0;
      wb_csr_wdata_reg <= 0;
      wb_csr_rdata_reg <= 0;
    end else if (!mem2_wb_stall) begin
      wb_rd_addr_raw_reg <= mem2_rd_addr_reg;
      wb_insn_reg <= mem2_insn_reg;
      wb_alu_csr_result_reg <= mem2_alu_csr_result_reg;
      wb_pc_rdata_reg <= mem2_pc_rdata_reg;
      wb_pc_plus_4 <= mem2_pc_plus_4_reg;
      wb_result_src_reg <= mem2_result_src_reg;
      wb_carried_trap_reg <= mem2_trap_comb;
      wb_csr_addr_raw_reg <= mem2_csr_addr_reg;
      wb_valid_insn_reg <= mem2_valid_insn_reg;
      wb_intr_reg <= mem2_intr_reg;
      wb_rs1_rdata_reg <= mem2_rs1_rdata_reg;
      wb_rs2_rdata_reg <= mem2_rs2_rdata_reg;
      wb_rs1_addr_reg <= mem2_rs1_addr_reg;
      wb_rs2_addr_reg <= mem2_rs2_addr_reg;
      wb_mem_rdata_reg <= mem_rdata_comb;
      wb_mem_rmask_reg <= mem_rmask_comb;
      wb_mem_wdata_reg <= mem2_mem_wdata_reg;
      wb_mem_wmask_reg <= mem2_mem_wmask_reg;
      wb_pc_wdata_reg <= mem2_pc_wdata_reg;
      wb_csr_wdata_reg <= mem2_csr_wdata_reg;
      wb_csr_rdata_reg <= mem2_csr_rdata_reg;
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
    if (maindec_trap_valid_comb) begin
      id_trap_comb = '{
          valid: 1,
          is_interrupt: 0,
          insn: id_insn_reg,
          mcause: maindec_mcause_comb,
          pc: id_pc_rdata_reg,
          next_pc: trap_handler_addr_reg,
          rs1_addr: 0,
          rs2_addr: 0,
          rd_addr: 0,
          rs1_rdata: 0,
          rs2_rdata: 0,
          rd_wdata: 0
      };
    end else begin
      id_trap_comb = '{default: 0};
    end
  end

  always_comb begin
    if (ex_carried_trap_reg.valid) begin
      ex_trap_comb = ex_carried_trap_reg;
    end else if (ex_misaligned_jump_or_branch_comb) begin
      ex_trap_comb = '{
          valid: 1,
          is_interrupt: 0,
          insn: ex_insn_reg,
          mcause: TRAP_CODE_INSTR_ADDR_MISALIGNED,
          pc: ex_pc_rdata_reg,
          next_pc: trap_handler_addr_reg,
          rs1_addr: ex_rs1_addr_raw_reg,
          rs2_addr: ex_rs2_addr_raw_reg,
          rd_addr: ex_rd_addr_raw_reg,
          rs1_rdata: ex_rs1_rdata_comb,
          rs2_rdata: ex_rs2_rdata_comb,
          rd_wdata: 0
      };
    end else begin
      ex_trap_comb = '{default: 0};
    end
  end

  always_comb begin
    if (mem1_carried_trap_reg.valid) begin
      mem1_trap_comb = mem1_carried_trap_reg;
    end else if (mem1_store_trap_valid) begin
      mem1_trap_comb = '{
          valid: 1,
          is_interrupt: 0,
          insn: mem1_insn_reg,
          mcause: MEM1_store_trap_code,
          pc: mem1_pc_rdata_reg,
          next_pc: trap_handler_addr_reg,
          rs1_addr: mem1_rs1_addr_reg,
          rs2_addr: mem1_rs2_addr_reg,
          rd_addr: mem1_rd_addr_reg,
          rs1_rdata: mem1_rs1_rdata_reg,
          rs2_rdata: mem1_rs2_rdata_reg,
          rd_wdata: 0
      };
    end else begin
      mem1_trap_comb = '{default: 0};
    end
  end

  always_comb begin
    if (mem2_carried_trap_reg.valid) begin
      mem2_trap_comb = mem2_carried_trap_reg;
    end else if (MEM2_load_trap_valid) begin
      mem2_trap_comb = '{
          valid: 1,
          is_interrupt: 0,
          insn: mem2_insn_reg,
          mcause: MEM2_load_trap_code,
          pc: mem2_pc_rdata_reg,
          next_pc: trap_handler_addr_reg,
          rs1_addr: mem2_rs1_addr_reg,
          rs2_addr: mem2_rs2_addr_reg,
          rd_addr: mem2_rd_addr_reg,
          rs1_rdata: mem2_rs1_rdata_reg,
          rs2_rdata: mem2_rs2_rdata_reg,
          rd_wdata: 0
      };
    end else begin
      mem2_trap_comb = '{default: 0};
    end
  end

  assign wb_trap_comb = wb_carried_trap_reg.valid ? wb_carried_trap_reg : '{default: 0};

  //////////////////////////////////////
  //
  //  HAZARD LOGIC
  //
  //
  ///////////////////////////////////////

  hazard_unit hazard_unit_inst (
      .EX_RS1_ADDR(ex_rs1_addr_actual_comb),
      .EX_RS2_ADDR(ex_rs2_addr_actual_comb),
      .MEM1_RD_ADDR(mem1_rd_addr_reg),
      .MEM2_RD_ADDR(mem2_rd_addr_reg),
      .WB_RD_ADDR(wb_rd_addr_actual_comb),
      .EX_RESULT_SRC(ex_result_src_reg),
      .MEM1_RESULT_SRC(mem1_result_src_reg),
      .MEM2_RESULT_SRC(mem2_result_src_reg),
      .ID_RS1_ADDR(id_rs1_addr_comb),
      .ID_RS2_ADDR(id_rs2_addr_comb),
      .EX_RD_ADDR(ex_rd_addr_actual_comb),
      .EX_PC_SRC(ex_pc_src_actual_comb),
      .EX_FORWARD_A(ex_forward_a_sel_comb),
      .EX_FORWARD_B(ex_forward_b_sel_comb),
      .ID_FORWARD_A(id_forward_a_comb),
      .ID_FORWARD_B(id_forward_b_comb),
      .IF_ID_FLUSH(if_id_flush),
      .ID_EX_FLUSH(id_ex_flush),
      .EX_MEM1_FLUSH(ex_mem1_flush),
      .MEM1_MEM2_FLUSH(mem1_mem2_flush),
      .MEM2_WB_FLUSH(mem2_wb_flush),
      .IF_ID_STALL(if_id_stall),
      .ID_EX_STALL(id_ex_stall),
      .MEM1_MEM2_STALL(mem1_mem2_stall),
      .MEM2_WB_STALL(mem2_wb_stall),
      .EX_MEM1_STALL(ex_mem1_stall),
      .EX_TRAP_VALID(ex_carried_trap_reg.valid),
      .MEM1_TRAP_VALID(mem1_carried_trap_reg.valid),
      .MEM2_TRAP_VALID(mem2_carried_trap_reg.valid),
      .WB_TRAP_VALID(wb_carried_trap_reg.valid),
      .AXIL_EN(axil_actual_en),
      .AXIL_DONE_READ(AXIL_DONE_READ),
      .AXIL_DONE_WRITE(AXIL_DONE_WRITE)
  );

  assign DMEM_ADDR  = mem1_alu_csr_result_reg[DMEM_ADDR_WIDTH-1:0];
  assign IMEM_ADDR  = if_a_pc_rdata_reg[IMEM_ADDR_WIDTH-1:0];
  assign DMEM_WDATA = mem_wdata_comb;
  assign DMEM_WMASK = mem_wmask_comb;

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
  assign rvfi_valid_next = mem2_wb_stall ? 0 : wb_valid_insn_reg;

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
    case (wb_csr_addr_actual_comb)
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
      rvfi_trap <= wb_trap_comb.valid;
      rvfi_intr <= wb_intr_reg;

      if (wb_trap_comb.valid) begin
        rvfi_insn <= wb_trap_comb.insn;
        rvfi_rs1_addr <= wb_trap_comb.rs1_addr;
        rvfi_rs2_addr <= wb_trap_comb.rs2_addr;
        rvfi_rs1_rdata <= wb_trap_comb.rs1_rdata;
        rvfi_rs2_rdata <= wb_trap_comb.rs2_rdata;

        rvfi_rd_addr <= wb_trap_comb.rd_addr;
        rvfi_rd_wdata <= wb_trap_comb.rd_wdata;

        rvfi_pc_rdata <= wb_trap_comb.pc;
        rvfi_pc_wdata <= wb_trap_comb.next_pc;

        rvfi_mem_addr <= wb_alu_csr_result_reg;
        rvfi_mem_rmask <= wb_mem_rmask_reg;
        rvfi_mem_wmask <= wb_mem_wmask_reg;
        rvfi_mem_rdata <= wb_mem_rdata_reg;
        rvfi_mem_wdata <= wb_mem_wdata_reg;
      end else begin
        rvfi_insn <= wb_insn_reg;
        rvfi_rs1_addr <= wb_rs1_addr_reg;
        rvfi_rs2_addr <= wb_rs2_addr_reg;
        rvfi_rs1_rdata <= wb_rs1_rdata_reg;
        rvfi_rs2_rdata <= wb_rs2_rdata_reg;

        rvfi_rd_addr <= wb_rd_addr_actual_comb;
        rvfi_rd_wdata <= wb_rd_wdata_comb;

        rvfi_pc_rdata <= wb_pc_rdata_reg;
        rvfi_pc_wdata <= wb_trap_comb.valid ? trap_handler_addr_reg : wb_pc_wdata_reg;

        rvfi_mem_addr <= wb_alu_csr_result_reg;
        rvfi_mem_rmask <= wb_mem_rmask_reg;
        rvfi_mem_wmask <= wb_mem_wmask_reg;
        rvfi_mem_rdata <= wb_mem_rdata_reg;
        rvfi_mem_wdata <= wb_mem_wdata_reg;
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

      rvfi_csr_mcycle_rdata <= is_csr_mcycleh ? {wb_csr_rdata_reg, 32'd0} :
          is_csr_mcycle  ? {32'd0, wb_csr_rdata_reg} :
          64'd0;
      rvfi_csr_minstret_rdata <= is_csr_minstreth ? {wb_csr_rdata_reg, 32'd0} :
          is_csr_minstret  ? {32'd0, wb_csr_rdata_reg} :
          64'd0;
      // csr rdata logic
      rvfi_csr_mcause_rdata <= is_csr_mcause ? wb_csr_rdata_reg : 32'd0;
      rvfi_csr_mtvec_rdata <= is_csr_mtvec ? wb_csr_rdata_reg : 32'd0;
      rvfi_csr_mepc_rdata <= is_csr_mepc ? wb_csr_rdata_reg : 32'd0;

      rvfi_csr_mcycle_wdata <= is_csr_mcycleh ? {wb_csr_wdata_reg, 32'd0} :
          is_csr_mcycle  ? {32'd0, wb_csr_wdata_reg} :
          64'd0;
      rvfi_csr_minstret_wdata <= is_csr_minstreth ? {wb_csr_wdata_reg, 32'd0} :
          is_csr_minstret  ? {32'd0, wb_csr_wdata_reg} :
          64'd0;
      rvfi_csr_mcause_wdata <= is_csr_mcause ? wb_csr_wdata_reg : 32'd0;
      rvfi_csr_mtvec_wdata <= is_csr_mtvec ? wb_csr_wdata_reg : 32'd0;
      rvfi_csr_mepc_wdata <= is_csr_mepc ? wb_csr_wdata_reg : 32'd0;

    end
  end
`endif
endmodule
