
module dtcore32 (
  input  logic        clk_i,
  input  logic        rst_i,
  input  logic [31:0] imem_rdata_i,
  input  logic [31:0] dmem_rdata_i,
  `ifdef RISCV_FORMAL
  output logic        rvfi_valid,
  output logic [63:0] rvfi_order,
  output logic [31:0] rvfi_insn,
  output logic        rvfi_trap,
  output logic        rvfi_halt,
  output logic        rvfi_intr,
  output logic [ 1:0] rvfi_mode,
  output logic [ 1:0] rvfi_ixl,
  output logic [ 4:0] rvfi_rs1_addr,
  output logic [ 4:0] rvfi_rs2_addr,
  output logic [31:0] rvfi_rs1_rdata,
  output logic [31:0] rvfi_rs2_rdata,
  output logic [ 4:0] rvfi_rd_addr,
  output logic [31:0] rvfi_rd_wdata,
  output logic [31:0] rvfi_pc_rdata,
  output logic [31:0] rvfi_pc_wdata,
  output logic [31:0] rvfi_mem_addr,
  output logic [ 3:0] rvfi_mem_rmask,
  output logic [ 3:0] rvfi_mem_wmask,
  output logic [31:0] rvfi_mem_rdata,
  output logic [31:0] rvfi_mem_wdata,
  output logic [63:0] rvfi_csr_mcycle_rmask,
  output logic [63:0] rvfi_csr_mcycle_wmask,
  output logic [63:0] rvfi_csr_mcycle_rdata,
  output logic [63:0] rvfi_csr_mcycle_wdata,
  output logic [63:0] rvfi_csr_minstret_rmask,
  output logic [63:0] rvfi_csr_minstret_wmask,
  output logic [63:0] rvfi_csr_minstret_rdata,
  output logic [63:0] rvfi_csr_minstret_wdata,
  output logic [31:0] rvfi_csr_mcause_rmask,
  output logic [31:0] rvfi_csr_mcause_wmask,
  output logic [31:0] rvfi_csr_mcause_rdata,
  output logic [31:0] rvfi_csr_mcause_wdata,
  output logic [31:0] rvfi_csr_mepc_rmask,
  output logic [31:0] rvfi_csr_mepc_wmask,
  output logic [31:0] rvfi_csr_mepc_rdata,
  output logic [31:0] rvfi_csr_mepc_wdata,
  output logic [31:0] rvfi_csr_mtvec_rmask,
  output logic [31:0] rvfi_csr_mtvec_wmask,
  output logic [31:0] rvfi_csr_mtvec_rdata,
  output logic [31:0] rvfi_csr_mtvec_wdata,
  `endif
  output logic [31:0] imem_addr_o,
  output logic [31:0] dmem_addr_o,
  output logic [31:0] dmem_wdata_o,
  output logic [ 3:0] dmem_wmask_o
);
  import params_pkg::*;

  ///////////////////////////////////////////////
  //
  //  SIGNAL DECLARATIONS
  //
  //
  ///////////////////////////////////////////////
  logic IF_stall;
  logic ID_stall;

  logic ID_flush;
  logic EX_flush;
  logic MEM1_flush;
  logic MEM2_flush;
  logic WB_flush;

  trap_info_t IF_trap;
  trap_info_t ID_trap;
  trap_info_t EX_trap;
  trap_info_t MEM1_trap;
  trap_info_t MEM2_trap;
  trap_info_t WB_trap;

  pipeline_data_t IF_pipeline_data;
  pipeline_data_t ID_pipeline_data;
  pipeline_data_t EX_pipeline_data;
  pipeline_data_t MEM1_pipeline_data;
  pipeline_data_t MEM2_pipeline_data;
  pipeline_data_t WB_pipeline_data;

  logic ID_rst;
  logic EX_rst;
  logic MEM1_rst;
  logic MEM2_rst;
  logic WB_rst;
  logic jump_branch_trap_valid;
  trap_code_e jump_branch_trap_code;

  // instruction fetch signals
  logic [31:0] next_imem_addr;
  logic [31:0] EX_pc_wdata;
  logic [31:0] trap_handler_addr;
  logic [31:0] imem_addr_plus_4;
  // INSTRUCTION DECODE specific signals
  logic decoded_jump;
  logic decoded_branch;
  logic decoded_pc_target_alu_src;
  logic [31:0] rs1_rdata_regfile;
  logic [31:0] rs2_rdata_regfile;
  logic [4:0] decoded_rd_addr;
  logic [4:0] decoded_rs1_addr;
  logic [4:0] decoded_rs2_addr;
  logic [1:0] decoded_result_src;
  logic [3:0] decoded_alu_control;
  logic decoded_csr_write_src;
  logic [1:0] decoded_alu_a_src;
  csr_addr_e decoded_csr_addr;
  logic decoded_alu_b_src;
  logic [1:0] decoded_csr_wtype;
  logic [31:0] rs1_rdata_ID_forwarded;
  logic [31:0] rs2_rdata_ID_forwarded;
  imm_code_e decoded_imm_src;
  logic [31:0] decoded_imm_ext;
  logic [1:0] decoded_mem_stype;
  logic [2:0] decoded_mem_ltype;
  opcode_e decoded_op;
  logic [2:0] decoded_funct3;
  logic funct7b5;
  logic [6:0] decoded_funct7;
  funct12_e decoded_funct12;
  alu_opcode_e decoded_alu_op;
  trap_code_e alu_decoder_trap_code;
  logic alu_decoder_trap_valid;
  trap_code_e main_decoder_trap_code;
  logic main_decoder_trap_valid;
  logic valid_decoded_rs1_addr;
  logic valid_decoded_rs2_addr;
  logic valid_decoded_rd_addr;
  logic rs1_ID_forward_sel;
  logic rs2_ID_forward_sel;
  // EXECUTE stage specific signals
  logic [31:0] rs2_rdata_EX_forwarded;
  logic [31:0] rs1_rdata_EX_forwarded;
  logic [1:0] rs1_EX_forward_sel;
  logic [1:0] rs2_EX_forward_sel;
  logic [31:0] alu_result;
  logic [1:0] alu_a_src;
  logic [31:0] csr_raw_wdata;
  logic next_pc_sel;
  logic [31:0] jump_branch_pc_target;
  logic [31:0] alu_operand_a;
  logic [31:0] alu_operand_b;
  logic [31:0] base_jump_branch_addr;
  logic branch_cond;
  logic [1:0] result_src_lsb2;
  logic misaligned_jump_or_branch;
  // DATA MEMORY 1 stage
  trap_code_e store_trap_code;
  logic store_trap_valid;
  logic [3:0] MEM1_mem_wmask;
  logic [31:0] MEM1_mem_wdata;
  // DATA MEMORY 2 stage
  logic [31:0] MEM2_mem_rdata;
  logic [3:0] MEM2_mem_rmask;
  logic load_trap_valid;
  trap_code_e load_trap_code;
  // WRITEBACK stage specific signals
  logic [31:0] WB_csr_rdata;
  logic [31:0] WB_csr_wdata;
  logic [31:0] WB_result;
  logic [31:0] WB_rd_wdata;
  logic [31:0] WB_csr_rmask;
  logic [31:0] WB_csr_wmask;
  // csr signals
  logic is_csr_mcycleh;
  logic is_csr_mcycle;
  logic is_csr_minstreth;
  logic is_csr_minstret;
  logic is_csr_mcause;
  logic is_csr_mtvec;
  logic is_csr_mepc;



  assign ID_rst   = rst_i || ID_flush || (!ID_stall & IF_stall);
  assign EX_rst   = rst_i || EX_flush || ID_stall;
  assign MEM1_rst = rst_i || MEM1_flush;
  assign MEM2_rst = rst_i || MEM2_flush;
  assign WB_rst   = rst_i || WB_flush;

  //////////////////////////////////////
  //
  //  INSTRUCTION FETCH STAGE
  //
  //
  ///////////////////////////////////////
  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      IF_pipeline_data <= ZERO_PIPELINE_DATA;
    end else if (WB_trap.valid) begin  // jump to trap handler if retired instrucion has a trap
      IF_pipeline_data <= '{
        pc_rdata: trap_handler_addr,
        intr: 1,
        carried_trap: ZERO_TRAP,
        alu_control: ZERO_ALU_CONTROL,
        csr_addr: ZERO_CSR_ADDR,
        default: '0
      };
    end else if (!IF_stall) begin
      IF_pipeline_data <= '{
        pc_rdata: next_imem_addr,
        intr: 0,
        carried_trap: ZERO_TRAP,
        alu_control: ZERO_ALU_CONTROL,
        csr_addr: ZERO_CSR_ADDR,
        default: '0
      };
    end
  end
  assign imem_addr_plus_4 = IF_pipeline_data.pc_rdata + 4;
  assign next_imem_addr   = next_pc_sel ? jump_branch_pc_target : imem_addr_plus_4;



  //////////////////////////////////////
  //
  //  INSTRUCTION DECODE STAGE
  //
  //
  ///////////////////////////////////////
  always_ff @(posedge clk_i) begin
    if (ID_rst) begin
      ID_pipeline_data <= ZERO_PIPELINE_DATA;
    end else if (IF_trap.valid) begin
      ID_pipeline_data <= '{
        valid: 1,
        insn: NOP_INSTRUCTION,
        carried_trap: IF_trap,
        alu_control: ZERO_ALU_CONTROL,
        csr_addr: ZERO_CSR_ADDR,
        default: '0
      };
    end else if (!ID_stall) begin
      ID_pipeline_data <= '{
        valid: 1,
        insn: imem_rdata_i,
        pc_rdata: IF_pipeline_data.pc_rdata,
        pc_plus_4: IF_pipeline_data.pc_plus_4,
        intr: IF_pipeline_data.intr,
        carried_trap: trap_info_t'(ZERO_TRAP),
        alu_control: ZERO_ALU_CONTROL,
        csr_addr: ZERO_CSR_ADDR,
        default: '0
      };
    end
  end

  assign decoded_op       = opcode_e'(ID_pipeline_data.insn[6:0]);
  assign decoded_funct3   = ID_pipeline_data.insn[14:12];
  assign funct7b5         = ID_pipeline_data.insn[30];
  assign decoded_funct7   = ID_pipeline_data.insn[31:25];
  assign decoded_funct12  = funct12_e'(ID_pipeline_data.insn[31:20]);
  assign decoded_rs1_addr = valid_decoded_rs1_addr ? ID_pipeline_data.insn[19:15] : 0;
  assign decoded_rs2_addr = valid_decoded_rs2_addr ? ID_pipeline_data.insn[24:20] : 0;
  assign decoded_rd_addr  = valid_decoded_rd_addr ? ID_pipeline_data.insn[11:7] : 0;
  assign decoded_csr_addr = (decoded_csr_wtype != 0) ? csr_addr_e'(ID_pipeline_data.insn[31:20]) : CSR_ADDR_NO_ADDR;
  // select forwarded rs1 or rs2 rdata if needed
  assign rs1_rdata_ID_forwarded = rs1_ID_forward_sel ? WB_rd_wdata : rs1_rdata_regfile;
  assign rs2_rdata_ID_forwarded = rs2_ID_forward_sel ? WB_rd_wdata : rs2_rdata_regfile;


  extend extend_inst (
    .insn_i(ID_pipeline_data.insn),
    .imm_src_i(decoded_imm_src),
    .imm_ext_o(decoded_imm_ext)
  );

  main_decoder main_decoder_inst (
    .op_i(decoded_op),
    .funct3_i(decoded_funct3),
    .funct7_i(decoded_funct7),
    .funct12_i(decoded_funct12),
    .rs1_addr_i(decoded_rs1_addr),
    .rd_addr_i(decoded_rd_addr),
    .valid_rd_addr_o(valid_decoded_rd_addr),
    .valid_rs1_addr_o(valid_decoded_rs1_addr),
    .valid_rs2_addr_o(valid_decoded_rs2_addr),
    .imm_src_o(decoded_imm_src),
    .alu_a_src_o(decoded_alu_a_src),
    .alu_b_src_o(decoded_alu_b_src),
    .mem_stype_o(decoded_mem_stype),
    .result_src_o(decoded_result_src),
    .branch_o(decoded_branch),
    .alu_op_o(decoded_alu_op),
    .jump_o(decoded_jump),
    .pc_target_alu_src_o(decoded_pc_target_alu_src),
    .mem_ltype_o(decoded_mem_ltype),
    .csr_wtype_o(decoded_csr_wtype),
    .csr_write_src_o(decoded_csr_write_src),
    .main_decoder_trap_code_o(main_decoder_trap_code),
    .main_decoder_trap_valid_o(main_decoder_trap_valid)
  );

  alu_decoder alu_decoder_inst (
    .alu_op_i(decoded_alu_op),
    .funct7b5(funct7b5),
    .funct3_i(decoded_funct3),
    .alu_control_o(decoded_alu_control),
    .alu_decoder_trap_code_o(alu_decoder_trap_code),
    .alu_decoder_trap_valid_o(alu_decoder_trap_valid)
  );


  // register file
  dtcore32_regfile dtcore32_regfile_inst (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .rs1_addr_i(decoded_rs1_addr),
    .rs2_addr_i(decoded_rs2_addr),
    .rd_addr_i(WB_pipeline_data.rd_addr),
    .reg_wr_data_i(WB_rd_wdata),
    .rs1_rdata_o(rs1_rdata_regfile),
    .rs2_rdata_o(rs2_rdata_regfile)
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

  // ID/EX register
  always_ff @(posedge clk_i) begin
    if (EX_rst) begin
      EX_pipeline_data <= ZERO_PIPELINE_DATA;
    end else if (ID_trap.valid) begin
      EX_pipeline_data <= '{
        insn: NOP_INSTRUCTION,
        carried_trap: ID_trap,
        alu_control: ZERO_ALU_CONTROL,
        csr_addr: ZERO_CSR_ADDR,
        default: 0
      };
    end else begin
      EX_pipeline_data <= '{
        insn: ID_pipeline_data.insn,
        valid: ID_pipeline_data.valid,
        intr: ID_pipeline_data.intr,
        result_src: ID_pipeline_data.result_src,
        mem_ltype: ID_pipeline_data.mem_ltype,
        jump: ID_pipeline_data.jump,
        branch: ID_pipeline_data.branch,
        alu_control: ID_pipeline_data.alu_control,
        alu_a_src: ID_pipeline_data.alu_a_src,
        alu_b_src: ID_pipeline_data.alu_b_src,
        pc_target_alu_src: ID_pipeline_data.pc_target_alu_src,
        rs1_rdata: ID_pipeline_data.rs1_rdata,
        rs2_rdata: ID_pipeline_data.rs2_rdata,
        rs1_addr: ID_pipeline_data.rs1_addr,
        rs2_addr: ID_pipeline_data.rs2_addr,
        rd_addr: ID_pipeline_data.rd_addr,
        imm_ext: ID_pipeline_data.imm_ext,
        pc_plus_4: ID_pipeline_data.pc_plus_4,
        csr_addr: decoded_csr_addr,
        csr_write_src: ID_pipeline_data.csr_write_src,
        csr_wtype: ID_pipeline_data.csr_wtype,
        carried_trap: trap_info_t'(ZERO_TRAP),
        default: 0
      };
    end
  end
  assign jump_branch_pc_target = base_jump_branch_addr + EX_pipeline_data.imm_ext;
  // used for rvfi signals
  assign EX_pc_wdata               = next_pc_sel ? jump_branch_pc_target : EX_pipeline_data.pc_plus_4;
  assign next_pc_sel               = (EX_pipeline_data.jump | (EX_pipeline_data.branch & branch_cond));
  assign misaligned_jump_or_branch = jump_branch_pc_target[1] | jump_branch_pc_target[0];
  assign jump_branch_trap_valid    = (next_pc_sel && misaligned_jump_or_branch);
  assign jump_branch_trap_code = TRAP_CODE_INSTR_ADDR_MISALIGNED;



  mux2 i_mux2_1 (.in0(rs2_rdata_EX_forwarded), .in1(EX_pipeline_data.imm_ext), .sel(EX_pipeline_data.alu_b_src), .y(alu_operand_b));
  mux2 i_mux2_2 (.in0(EX_pipeline_data.pc_rdata), .in1(rs1_rdata_EX_forwarded), .sel(EX_pipeline_data.pc_target_alu_src), .y(base_jump_branch_addr));
  mux2 i_mux2_3 (.in0(rs1_rdata_EX_forwarded), .in1(EX_pipeline_data.imm_ext), .sel(EX_pipeline_data.csr_write_src), .y(csr_raw_wdata));

  mux4 i_mux4_1 (.in0(EX_pipeline_data.rs1_rdata), .in1(WB_result), .in2(MEM2_pipeline_data.alu_result), .in3(MEM1_pipeline_data.alu_result), .sel(rs1_EX_forward_sel), .y(rs1_rdata_EX_forwarded));
  mux4 i_mux4_2 (.in0(rs1_rdata_EX_forwarded), .in1(0), .in2(EX_pipeline_data.pc_rdata), .in3(0), .sel(EX_pipeline_data.alu_a_src), .y(alu_operand_a));
  mux4 i_mux4_3 (.in0(EX_pipeline_data.rs2_rdata), .in1(WB_result), .in2(MEM2_pipeline_data.alu_result), .in3(MEM1_pipeline_data.alu_result), .sel(rs2_EX_forward_sel), .y(rs2_rdata_EX_forwarded));
  // calculates the instruction specific alu result
  alu i_alu (.a_i(alu_operand_a), .b_i(alu_operand_b), .control_i(EX_pipeline_data.alu_control), .branch_cond_o(branch_cond), .result_o(alu_result));


  //////////////////////////////////////
  //
  //  DATA MEMORY STAGE 1
  //
  //
  ///////////////////////////////////////
  // EX/MEM1 register
  always_ff @(posedge clk_i) begin
    if (MEM1_rst) begin
      MEM1_pipeline_data = ZERO_PIPELINE_DATA;
    end else if (EX_trap.valid) begin
      MEM1_pipeline_data = '{
        insn: NOP_INSTRUCTION,
        carried_trap: EX_trap,
        alu_control: ZERO_ALU_CONTROL,
        csr_addr: ZERO_CSR_ADDR,
        default: 0
      };

    end else begin
      MEM1_pipeline_data = '{
        insn: EX_pipeline_data.insn,
        valid: EX_pipeline_data.valid,
        intr: EX_pipeline_data.intr,
        result_src: EX_pipeline_data.result_src,
        mem_ltype: EX_pipeline_data.mem_ltype,
        mem_stype: EX_pipeline_data.mem_stype,
        alu_result: EX_pipeline_data.alu_result,
        mem_raw_wdata: rs2_rdata_EX_forwarded,
        rd_addr: EX_pipeline_data.rd_addr,
        pc_rdata: EX_pipeline_data.pc_rdata,
        pc_plus_4: EX_pipeline_data.pc_plus_4,
        csr_addr: EX_pipeline_data.csr_addr,
        csr_raw_wdata: csr_raw_wdata,
        csr_wtype: EX_pipeline_data.csr_wtype,
        rs1_rdata: rs1_rdata_EX_forwarded,
        rs2_rdata: rs2_rdata_EX_forwarded,
        rs1_addr: EX_pipeline_data.rs1_addr,
        rs2_addr: EX_pipeline_data.rs2_addr,
        pc_wdata: EX_pc_wdata,
        carried_trap: trap_info_t'(ZERO_TRAP),
        alu_control: ZERO_ALU_CONTROL,
        default: 0
      };
    end
  end

  store_unit store_unit_inst (
    .store_size_i(MEM1_pipeline_data.mem_stype),
    .addr_lsb2_i(MEM1_pipeline_data.alu_result[1:0]),
    .wdata_unformatted_i(MEM1_pipeline_data.mem_raw_wdata),
    .store_trap_o(store_trap_valid),
    .trap_code_o(store_trap_code),
    .wmask_o(MEM1_mem_wmask),
    .wdata_formatted_o(MEM1_mem_wdata)
  );
  //////////////////////////////////////
  //
  //  DATA MEMORY STAGE 2
  //
  //
  ///////////////////////////////////////
  always_ff @(posedge clk_i) begin
    if (MEM2_rst) begin
      MEM2_pipeline_data = ZERO_PIPELINE_DATA;
    end else if (MEM1_trap.valid) begin
      MEM2_pipeline_data = '{
        insn: NOP_INSTRUCTION,
        carried_trap: MEM1_trap,
        alu_control: ZERO_ALU_CONTROL,
        csr_addr: ZERO_CSR_ADDR,
        default: '0
      };
    end else begin
      MEM2_pipeline_data = '{
        insn: MEM1_pipeline_data.insn,
        valid: MEM1_pipeline_data.valid,
        intr: MEM1_pipeline_data.intr,
        result_src: MEM1_pipeline_data.result_src,
        mem_ltype: MEM1_pipeline_data.mem_ltype,
        alu_result: MEM1_pipeline_data.alu_result,
        rd_addr: MEM1_pipeline_data.rd_addr,
        pc_rdata: MEM1_pipeline_data.pc_rdata,
        pc_plus_4: MEM1_pipeline_data.pc_plus_4,
        csr_addr: MEM1_pipeline_data.csr_addr,
        csr_raw_wdata: MEM1_pipeline_data.csr_raw_wdata,
        csr_wtype: MEM1_pipeline_data.csr_wtype,
        rs1_rdata: MEM1_pipeline_data.rs1_rdata,
        rs2_rdata: MEM1_pipeline_data.rs2_rdata,
        rs1_addr: MEM1_pipeline_data.rs1_addr,
        rs2_addr: MEM1_pipeline_data.rs2_addr,
        pc_wdata: MEM1_pipeline_data.pc_wdata,
        mem_wmask: MEM1_mem_wmask,
        mem_wdata: MEM1_mem_wdata,
        carried_trap: trap_info_t'(ZERO_TRAP),
        alu_control: ZERO_ALU_CONTROL,
        default: 0
      };
    end
  end

  load_unit load_unit_inst (
    .load_type(MEM2_pipeline_data.mem_ltype),
    .addr_lsb2(MEM2_pipeline_data.alu_result[1:0]),
    .rdata_unformatted_i(dmem_rdata_i),
    .load_trap_o(load_trap_valid),
    .trap_code_o(load_trap_code),
    .rmask_o(MEM2_mem_rmask),
    .rdata_formatted_o(MEM2_mem_rdata)
  );

  //////////////////////////////////////
  //
  //  WRITEBACK STAGE
  //
  //
  ///////////////////////////////////////

  // pipeline to WB stage
  always_ff @(posedge clk_i) begin
    if (WB_rst) begin
      WB_pipeline_data <= ZERO_PIPELINE_DATA;
    end else if (MEM2_trap.valid) begin
      WB_pipeline_data <= '{
        insn: NOP_INSTRUCTION,
        carried_trap: MEM2_trap,
        alu_control: ZERO_ALU_CONTROL,
        csr_addr: ZERO_CSR_ADDR,
        default: '0
      };
    end else begin
      WB_pipeline_data <= '{
        insn: MEM2_pipeline_data.insn,
        valid: MEM2_pipeline_data.valid,
        intr: MEM2_pipeline_data.intr,
        alu_result: MEM2_pipeline_data.alu_result,
        pc_rdata: MEM2_pipeline_data.pc_rdata,
        pc_plus_4: MEM2_pipeline_data.pc_plus_4,
        result_src: MEM2_pipeline_data.result_src,
        csr_addr: MEM2_pipeline_data.csr_addr,
        csr_raw_wdata: MEM2_pipeline_data.csr_raw_wdata,
        csr_wtype: MEM2_pipeline_data.csr_wtype,
        rs1_addr: MEM2_pipeline_data.rs1_addr,
        rs2_addr: MEM2_pipeline_data.rs2_addr,
        rs1_rdata: MEM2_pipeline_data.rs1_rdata,
        rs2_rdata: MEM2_pipeline_data.rs2_rdata,
        rd_addr: MEM2_pipeline_data.rd_addr,
        mem_rmask: MEM2_mem_rmask,
        mem_rdata: MEM2_mem_rdata,
        mem_wdata: MEM2_pipeline_data.mem_wdata,
        mem_wmask: MEM2_pipeline_data.mem_wmask,
        pc_wdata: MEM2_pipeline_data.pc_wdata,
        carried_trap: trap_info_t'(ZERO_TRAP),
        alu_control: ZERO_ALU_CONTROL,
        default: '0
      };

    end
  end
  // disable register and csr writes for an excepted instruction
  assign WB_rd_wdata = (WB_pipeline_data.rd_addr != 0) ? WB_result : 0;

  always_comb begin
    unique case (WB_pipeline_data.result_src)
      2'b00: WB_result = WB_pipeline_data.alu_result;
      2'b01: WB_result = WB_pipeline_data.mem_rdata;
      2'b10: WB_result = WB_pipeline_data.pc_plus_4;
      2'b11: WB_result = WB_csr_rdata;
    endcase
  end

  csr_regfile csr_regfile_inst (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .csr_addr_i(WB_pipeline_data.csr_addr),
    .WB_rd_addr_i(WB_pipeline_data.rd_addr),
    .WB_valid_insn_i(WB_pipeline_data.valid),
    .WB_trap_i(WB_trap),
    .csr_wtype_i(WB_pipeline_data.csr_wtype),
    .csr_woperand(WB_pipeline_data.csr_raw_wdata),
    .trap_handler_addr_o(trap_handler_addr),
    .csr_rdata_o(WB_csr_rdata),
    .csr_wdata_o(WB_csr_wdata),
    .csr_rmask_o(WB_csr_rmask),
    .csr_wmask_o(WB_csr_wmask)
  );

  //////////////////////////////////////
  //
  //  HAZARD LOGIC
  //
  //
  ///////////////////////////////////////

  assign result_src_lsb2 = EX_pipeline_data.result_src[1:0];

  dtcore32_hazard_unit dtcore32_hazard_unit_inst (
    .EX_rs1_addr_i(EX_pipeline_data.rs1_addr),
    .EX_rs2_addr_i(EX_pipeline_data.rs2_addr),
    .MEM1_rd_addr_i(MEM1_pipeline_data.rd_addr),
    .MEM2_rd_addr_i(MEM2_pipeline_data.rd_addr),
    .WB_rd_addr_i(WB_pipeline_data.rd_addr),
    .EX_result_src_lsb2_i(result_src_lsb2),
    .ID_rs1_addr_i(ID_pipeline_data.rs1_addr),
    .ID_rs2_addr_i(ID_pipeline_data.rs2_addr),
    .EX_rd_addr_i(EX_pipeline_data.rd_addr),
    .EX_pc_src_i(next_pc_sel),
    .EX_forward_a_o(rs1_EX_forward_sel),
    .EX_forward_b_o(rs2_EX_forward_sel),
    .ID_forward_a_o(rs1_ID_forward_sel),
    .ID_forward_b_o(rs2_ID_forward_sel),
    .ID_flush_o(ID_flush),
    .EX_flush_o(EX_flush),
    .MEM1_flush_o(MEM1_flush),
    .MEM2_flush_o(MEM2_flush),
    .WB_flush_o(WB_flush),
    .IF_stall_o(IF_stall),
    .ID_stall_o(ID_stall),
    .ID_trap_valid_i(ID_trap.valid),
    .EX_trap_valid_i(EX_trap.valid),
    .MEM1_trap_valid_i(MEM1_trap.valid),
    .MEM2_trap_valid_i(MEM2_trap.valid),
    .WB_trap_valid_i(WB_trap.valid)
  );
  //////////////////////////////////////
  //
  //  TRAP LOGIC
  //
  //
  ///////////////////////////////////////

  trap_control i_trap_control (
    .IF_pc_i             (IF_pipeline_data.pc_rdata),
    .ID_pc_i                  (ID_pipeline_data.pc_rdata                  ),
    .EX_pc_i                  (EX_pipeline_data.pc_rdata                  ),
    .MEM1_pc_i                (MEM1_pipeline_data.pc_rdata                ),
    .MEM2_pc_i                (MEM2_pipeline_data.pc_rdata                ),
    .ID_carried_trap_i        (ID_pipeline_data.carried_trap        ),
    .EX_carried_trap_i        (EX_pipeline_data.carried_trap        ),
    .MEM1_carried_trap_i      (MEM1_pipeline_data.carried_trap      ),
    .MEM2_carried_trap_i      (MEM2_pipeline_data.carried_trap      ),
    .WB_carried_trap_i        (WB_pipeline_data.carried_trap        ),
    .main_decoder_trap_valid_i(main_decoder_trap_valid),
    .main_decoder_trap_code_i (main_decoder_trap_code ),
    .alu_decoder_trap_valid_i (alu_decoder_trap_valid ),
    .alu_decoder_trap_code_i  (alu_decoder_trap_code  ),
    .store_trap_valid_i       (store_trap_valid       ),
    .store_trap_code_i        (store_trap_code        ),
    .load_trap_valid_i        (load_trap_valid        ),
    .load_trap_code_i         (load_trap_code         ),
    .jump_branch_trap_valid_i (jump_branch_trap_valid ),
    .jump_branch_trap_code_i  (jump_branch_trap_code  ),
    .IF_trap_o                (IF_trap                ),
    .ID_trap_o                (ID_trap                ),
    .EX_trap_o                (EX_trap                ),
    .MEM1_trap_o              (MEM1_trap           ),
    .MEM2_trap_o              (MEM2_trap              ),
    .WB_trap_o                (WB_trap                )
  );


  assign dmem_addr_o  = MEM1_pipeline_data.alu_result;
  assign imem_addr_o  = IF_pipeline_data.pc_rdata;
  assign dmem_wdata_o = MEM1_mem_wdata;
  assign dmem_wmask_o = MEM1_mem_wmask;

  //////////////////////////////////////
  //
  //  FORMAL VERIFICATION
  //
  //
  ///////////////////////////////////////

  `ifdef RISCV_FORMAL
    assign is_csr_mcycleh   = (WB_pipeline_data.csr_addr == CSR_ADDR_MCYCLEH);
    assign is_csr_mcycle    = (WB_pipeline_data.csr_addr == CSR_ADDR_MCYCLE);
    assign is_csr_minstreth = (WB_pipeline_data.csr_addr == CSR_ADDR_MINSTRETH);
    assign is_csr_minstret  = (WB_pipeline_data.csr_addr == CSR_ADDR_MINSTRET);
    assign is_csr_mcause    = (WB_pipeline_data.csr_addr == CSR_ADDR_MCAUSE);
    assign is_csr_mtvec     = (WB_pipeline_data.csr_addr == CSR_ADDR_MTVEC);
    assign is_csr_mepc      = (WB_pipeline_data.csr_addr == CSR_ADDR_MEPC);
    always_ff @(posedge clk_i) begin
      if (rst_i) begin
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
        rvfi_valid <= 1;//WB_pipeline_data.valid;
        if (WB_pipeline_data.valid) rvfi_order <= rvfi_order + 1;
        rvfi_insn <= WB_pipeline_data.insn;
        rvfi_trap <= WB_trap.valid;
        rvfi_halt <= 0;
        rvfi_intr <= WB_pipeline_data.intr;
        rvfi_mode <= 3;
        rvfi_ixl <= 1;

        rvfi_rs1_addr <= 1;//WB_pipeline_data.rs1_addr;
        rvfi_rs2_addr <= 2;//WB_pipeline_data.rs2_addr;
        rvfi_rs1_rdata <= WB_pipeline_data.rs1_rdata;
        rvfi_rs2_rdata <= WB_pipeline_data.rs2_rdata;

        rvfi_rd_addr <= WB_pipeline_data.rd_addr;
        rvfi_rd_wdata <= WB_rd_wdata;

        rvfi_pc_rdata <= WB_pipeline_data.pc_rdata;
        rvfi_pc_wdata <= WB_trap.valid   ? trap_handler_addr :
          WB_pipeline_data.valid  ? WB_pipeline_data.pc_wdata :
          MEM1_pipeline_data.valid ? MEM1_pipeline_data.pc_wdata :
          MEM2_pipeline_data.valid ? MEM2_pipeline_data.pc_wdata :
          EX_pipeline_data.valid  ? EX_pipeline_data.pc_wdata :
          ID_pipeline_data.valid  ? ID_pipeline_data.pc_wdata :
          IF_pipeline_data.pc_wdata;

        rvfi_mem_addr <= WB_pipeline_data.alu_result;
        rvfi_mem_rmask <= WB_pipeline_data.mem_rmask;
        rvfi_mem_wmask <= WB_pipeline_data.mem_wmask;
        rvfi_mem_rdata <= WB_pipeline_data.mem_rdata;
        rvfi_mem_wdata <= WB_pipeline_data.mem_wdata;

        // make rmask and wmask cleared if an trap
        rvfi_csr_mcycle_wmask <= is_csr_mcycleh ? {WB_csr_wmask, 32'd0}:
          is_csr_mcycle  ? {32'd0, WB_csr_wmask} :
          64'd0;
        rvfi_csr_minstret_wmask <= is_csr_minstreth ? {WB_csr_wmask, 32'd0} :
          is_csr_minstret  ? {32'd0, WB_csr_wmask} :
          64'd0;
        rvfi_csr_mcause_wmask <= is_csr_mcause ? WB_csr_wmask : 32'd0;
        rvfi_csr_mepc_wmask <= is_csr_mepc ? WB_csr_wmask : 32'd0;
        rvfi_csr_mtvec_wmask <= is_csr_mtvec ? WB_csr_wmask : 32'd0;

        rvfi_csr_mcycle_rmask <= is_csr_mcycleh ? {WB_csr_rmask, 32'd0} :
          is_csr_mcycle  ? {32'd0, WB_csr_rmask} :
          64'd0;
        rvfi_csr_minstret_rmask <= is_csr_minstreth ? {WB_csr_rmask, 32'd0} :
          is_csr_minstret  ? {32'd0, WB_csr_rmask} :
          64'd0;
        rvfi_csr_mcause_rmask <= is_csr_mcause ? WB_csr_rmask : 32'd0;
        rvfi_csr_mtvec_rmask <= is_csr_mtvec ? WB_csr_rmask : 32'd0;
        rvfi_csr_mepc_rmask <= is_csr_mepc ? WB_csr_rmask : 32'd0;

        rvfi_csr_mcycle_rdata <= is_csr_mcycleh ? {WB_csr_rdata, 32'd0} :
          is_csr_mcycle  ? {32'd0, WB_csr_rdata} :
          64'd0;
        rvfi_csr_minstret_rdata <= is_csr_minstreth ? {WB_csr_rdata, 32'd0} :
          is_csr_minstret  ? {32'd0, WB_csr_rdata} :
          64'd0;
        rvfi_csr_mcause_rdata <= is_csr_mcause ? WB_csr_rdata : 32'd0;
        rvfi_csr_mtvec_rdata <= is_csr_mtvec ? WB_csr_rdata : 32'd0;
        rvfi_csr_mepc_rdata <= is_csr_mepc ? WB_csr_rdata : 32'd0;

        rvfi_csr_mcycle_wdata <= is_csr_mcycleh ? {WB_csr_wdata, 32'd0} :
          is_csr_mcycle  ? {32'd0, WB_csr_wdata} :
          64'd0;
        rvfi_csr_minstret_wdata <= is_csr_minstreth ? {WB_csr_wdata, 32'd0} :
          is_csr_minstret  ? {32'd0, WB_csr_wdata} :
          64'd0;
        rvfi_csr_mcause_wdata <= is_csr_mcause ? WB_csr_wdata : 32'd0;
        rvfi_csr_mtvec_wdata <= is_csr_mtvec ? WB_csr_wdata : 32'd0;
        rvfi_csr_mepc_wdata <= is_csr_mepc ? WB_csr_wdata : 32'd0;

      end
    end




  `endif
endmodule
