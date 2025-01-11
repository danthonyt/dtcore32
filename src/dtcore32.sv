module dtcore32(
`ifdef RISCV_FORMAL
    output logic [`NRET        - 1 : 0] rvfi_valid_o,
    output logic [`NRET *   64 - 1 : 0] rvfi_order_o,
    output logic [`NRET * `ILEN - 1 : 0] rvfi_insn_o,
    output logic [`NRET        - 1 : 0] rvfi_trap_o,
    output logic [`NRET        - 1 : 0] rvfi_halt_o,
    output logic [`NRET        - 1 : 0] rvfi_intr_o,
    output logic [`NRET * 2    - 1 : 0] rvfi_mode_o,
    output logic [`NRET * 2    - 1 : 0] rvfi_ixl_o,

    output logic [`NRET *    5 - 1 : 0] rvfi_rs1_addr_o,
    output logic [`NRET *    5 - 1 : 0] rvfi_rs2_addr_o,
    output logic [`NRET * `XLEN - 1 : 0] rvfi_rs1_rdata_o,
    output logic [`NRET * `XLEN - 1 : 0] rvfi_rs2_rdata_o,

    output logic [`NRET *    5 - 1 : 0] rvfi_rd_addr_o,
    output logic [`NRET * `XLEN - 1 : 0] rvfi_rd_wdata_o,

    output logic [`NRET * `XLEN - 1 : 0] rvfi_pc_rdata_o,
    output logic [`NRET * `XLEN - 1 : 0] rvfi_pc_wdata_o,

    output logic [`NRET * `XLEN   - 1 : 0] rvfi_mem_addr_o,
    output logic [`NRET * `XLEN/8 - 1 : 0] rvfi_mem_rmask_o,
    output logic [`NRET * `XLEN/8 - 1 : 0] rvfi_mem_wmask_o,
    output logic [`NRET * `XLEN   - 1 : 0] rvfi_mem_rdata_o,
    output logic [`NRET * `XLEN   - 1 : 0] rvfi_mem_wdata_o,
`endif
    input logic           clk_i,
    input logic           rst_i,
    input logic   [31:0]  IMEM_rd_data_i,
    input logic   [31:0]  DMEM_rd_data_i,
    output logic [31:0]   IMEM_addr_o,
    output logic [31:0]   DMEM_addr_o,
    output logic [31:0]   DMEM_wr_data_o,
    output logic [1:0]    DMEM_wr_en_o,
    output logic          exception
  );
  // RISCV_FORMAL INTERFACE
  `ifdef RISCV_FORMAL

  assign IF_rvfi_insn_o = IF_instr_i;
  assign IF_rvfi_halt_o = 0;
  assign IF_rvfi_intr_o = 0;
  assign IF_rvfi_mode_o = 0;
  assign IF_rvfi_ixl_o = 1;


  assign  ID_rvfi_trap_o = ID_instr_exception;
  assign  ID_rvfi_rs1_addr_o = ID_instr_i[19:15];
  assign ID_rvfi_rs2_addr_o = ID_instr_i[24:20];
  assign ID_rvfi_rs1_rdata_o = ID_reg_data_1;
  assign ID_rvfi_rs2_rdata_o = ID_reg_data_2;


`endif
  // CHECK
  assign ID_instr_exception_o = ID_instr_exception;
  assign op = ID_instr_i[6:0];
  assign funct3 = ID_instr_i[14:12];
  assign funct7b5 = ID_instr_i[30];
  assign ID_dest_reg = isNop ? 0 : ID_instr_i[11:7];
  assign ID_src_reg_1 = isNop ? 0 : ID_instr_i[19:15];
  assign ID_src_reg_2 = isNop ? 0 : ID_instr_i[24:20];

  assign a1 = isNop ? 0 : ID_instr_i[19:15];
  assign a2 = isNop ? 0 : ID_instr_i[24:20];
  assign ID_imm_ext = isNop ? 0 : ID_imm_ext_sig;
  // DMEM interface
  logic [31:0] DMEM_addr;
  logic [31:0] DMEM_wr_data;
  logic [1:0]  DMEM_wr_en;
  //logic [31:0] DMEM_rd_data;

  // IMEM interface
  logic [31:0] IMEM_addr;
  //logic [31:0] IMEM_rd_data;

  // Instruction Fetch signals
  logic [31:0] IF_pc_tick;
  logic [31:0] IF_pc_plus_4;

  // Instruction decode signals
  logic [31:0] ID_instr;
  logic ID_reg_wr;
  logic [1:0] ID_result_src;
  logic [2:0] ID_load_size;
  logic [1:0] ID_mem_wr;
  logic ID_jump;
  logic ID_branch;
  logic [3:0] ID_alu_control;
  logic ID_alu_b_src;
  logic [1:0] ID_alu_a_src;
  logic ID_pc_target_alu_src;
  logic [2:0] ID_imm_src;
  logic [31:0] ID_reg_data_1;
  logic [31:0] ID_reg_data_2;
  logic [31:0] ID_pc;
  logic [19:15] ID_src_reg_1;
  logic [24:20] ID_src_reg_2;
  logic [11:7] ID_dest_reg;
  logic [31:0] ID_imm_ext;
  logic [31:0] ID_pc_plus_4;

  // Instruction execute signals
  logic EX_pc_src;
  logic EX_branch_cond;
  logic EX_reg_wr;
  logic [1:0] EX_result_src;
  logic [2:0] EX_load_size;
  logic [1:0] EX_mem_wr;
  logic EX_jump;
  logic EX_branch;
  logic [3:0] EX_alu_control;
  logic EX_alu_b_src;
  logic [1:0] EX_alu_a_src;
  logic EX_pc_target_alu_src;
  logic [31:0] EX_reg_data_1;
  logic [31:0] EX_reg_data_2;
  logic [31:0] EX_pc;
  logic [19:15] EX_src_reg_1;
  logic [24:20] EX_src_reg_2;
  logic [11:7] EX_dest_reg;
  logic [31:0] EX_imm_ext;
  logic [31:0] EX_pc_plus_4;
  logic [31:0] EX_src_a_tick;
  logic [31:0] EX_src_a;
  logic [31:0] EX_src_b;
  logic [31:0] EX_pc_target_src_a;
  logic [31:0] EX_wr_data;
  logic [31:0] EX_alu_result;
  logic [31:0] EX_pc_target;

  // data memory signals
  logic MEM_reg_wr;
  logic [1:0] MEM_result_src;
  logic [2:0] MEM_load_size;
  logic [11:7] MEM_dest_reg;
  logic [31:0] MEM_pc_plus_4;
  logic [31:0] MEM_rd_data;

  // write back signals
  logic WB_reg_wr;
  logic [1:0] WB_result_src;
  logic [31:0] WB_alu_result;
  logic [31:0] WB_rd_data;
  logic [11:7] WB_dest_reg;
  logic [31:0] WB_pc_plus_4;
  logic [31:0] WB_result;


  // hazard unit signals
  logic IF_stall;
  logic ID_stall;
  logic ID_flush;
  logic EX_flush;
  logic [1:0] EX_forward_a;
  logic [1:0] EX_forward_b;

  // DMEM interface
  assign DMEM_wr_data_o = DMEM_wr_data;
  assign DMEM_wr_en_o = DMEM_wr_en;

  // IMEM interface
  assign IMEM_addr_o = IMEM_addr;
  assign DMEM_addr_o = DMEM_addr;

  // Instruction Fetch stage
  ff_nen # (
           .WIDTH(32)
         )
         ff_nen_inst (
           .clk(clk_i),
           .rst(rst_i),
           .en_n(IF_stall),
           .d(IF_pc_tick),
           .q(IMEM_addr)
         );

  mux2to1 # (
            .WIDTH(32)
          )
          mux2to1_inst (
            .in0(IF_pc_plus_4),
            .in1(EX_pc_target),
            .sel(EX_pc_src),
            .out(IF_pc_tick)
          );

  adder # (
          .WIDTH(32)
        )
        adder_inst (
          .in1(IMEM_addr),
          .in2(32'd4),
          .sum(IF_pc_plus_4)
        );

  // IF/ID register
  always_ff @(posedge clk_i)
  begin
    if (rst_i || ID_flush)
    begin
      ID_instr <= 0;
      ID_pc <= 0;
      ID_pc_plus_4 <= 0;
    end
    else if (!ID_stall)
    begin
      ID_instr <= IMEM_rd_data_i;
      ID_pc <= IMEM_addr;
      ID_pc_plus_4 <= IF_pc_plus_4;
    end
  end


  //Instruction Decode stage
  assign ID_src_reg_1 = ID_instr[19:15];
  assign ID_src_reg_2 = ID_instr[24:20];
  assign ID_dest_reg = ID_instr[11:7];
  dtcore32_regfile  dtcore32_regfile_inst (
                      .clk(clk_i),
                      .we3(WB_reg_wr),
                      .rst(rst_i),
                      .a1(ID_instr[19:15]),
                      .a2(ID_instr[24:20]),
                      .a3(WB_dest_reg),
                      .wd3(WB_result),
                      .rd1(ID_reg_data_1),
                      .rd2(ID_reg_data_2)
                    );

  extend  extend_inst (
            .instr_data(ID_instr[31:7]),
            .imm_src(ID_imm_src),
            .imm_ext(ID_imm_ext)
          );

  dtcore32_controller  dtcore32_controller_inst (
                         .clk(clk_i),
                         .rst(rst_i),
                         .op(ID_instr[6:0]),
                         .funct3(ID_instr[14:12]),
                         .funct7b5(ID_instr[30]),
                         .ResultSrcD(ID_result_src),
                         .ALUASrcD(ID_alu_a_src),
                         .MemWriteD(ID_mem_wr),
                         .ALUControlD(ID_alu_control),
                         .ImmSrcD(ID_imm_src),
                         .LoadSizeD(ID_load_size),
                         .ALUBSrcD(ID_alu_b_src),
                         .RegWriteD(ID_reg_wr),
                         .JumpD(ID_jump),
                         .BranchD(ID_branch),
                         .PCTargetALUSrcD(ID_pc_target_alu_src),
                         .isNop(isNop),
                         .is_unknown_instruction(is_unknown_instruction)
                       );

  // ID/EX register
  always_ff @(posedge clk_i)
  begin
    if (rst_i || EX_flush)
    begin
      EX_reg_wr <= 0;
      EX_result_src <= 0;
      EX_load_size <= 0;
      EX_mem_wr <= 0;
      EX_jump <= 0;
      EX_branch <= 0;
      EX_alu_control <= 0;
      EX_alu_a_src <= 0;
      EX_alu_b_src <= 0;
      EX_pc_target_alu_src <= 0;
      EX_reg_data_1 <= 0;
      EX_reg_data_2 <= 0;
      EX_pc <= 0;
      EX_src_reg_1 <= 0;
      EX_src_reg_2 <= 0;
      EX_dest_reg <= 0;
      EX_imm_ext <= 0;
      EX_pc_plus_4 <= 0;
    end
    else
    begin
      EX_reg_wr <= ID_reg_wr;
      EX_result_src <= ID_result_src;
      EX_load_size <= ID_load_size;
      EX_mem_wr <= ID_mem_wr;
      EX_jump <= ID_jump;
      EX_branch <= ID_branch;
      EX_alu_control <= ID_alu_control;
      EX_alu_a_src <= ID_alu_a_src;
      EX_alu_b_src <= ID_alu_b_src;
      EX_pc_target_alu_src <= ID_pc_target_alu_src;
      EX_reg_data_1 <= ID_reg_data_1;
      EX_reg_data_2 <= ID_reg_data_2;
      EX_pc <= ID_pc;
      EX_src_reg_1 <= ID_src_reg_1;
      EX_src_reg_2 <= ID_src_reg_2;
      EX_dest_reg <= ID_dest_reg;
      EX_imm_ext <= ID_imm_ext;
      EX_pc_plus_4 <= ID_pc_plus_4;
    end
  end

  // Instruction Execute stage
  assign EX_pc_src = EX_jump | (EX_branch & EX_branch_cond);
  mux3to1 # (
            .WIDTH(32)
          )
          mux3to1_inst_EX1 (
            .in0(EX_reg_data_1),
            .in1(WB_result),
            .in2(DMEM_addr),
            .sel(EX_forward_a),
            .out(EX_src_a_tick)
          );
  mux3to1 # (
            .WIDTH(32)
          )
          mux3to1_inst_EX2 (
            .in0(EX_src_a_tick),
            .in1(32'd0),
            .in2(EX_pc),
            .sel(EX_alu_a_src),
            .out(EX_src_a)
          );
  mux3to1 # (
            .WIDTH(32)
          )
          mux3to1_inst_EX3 (
            .in0(EX_reg_data_2),
            .in1(WB_result),
            .in2(DMEM_addr),
            .sel(EX_forward_b),
            .out(EX_wr_data)
          );
  mux2to1 # (
            .WIDTH(32)
          )
          mux2to1_inst_EX1 (
            .in0(EX_wr_data),
            .in1(EX_imm_ext),
            .sel(EX_alu_b_src),
            .out(EX_src_b)
          );
  mux2to1 # (
            .WIDTH(32)
          )
          mux2to1_inst_EX2 (
            .in0(EX_pc),
            .in1(EX_src_a_tick),
            .sel(EX_pc_target_alu_src),
            .out(EX_pc_target_src_a)
          );
  adder # (
          .WIDTH(32)
        )
        adder_inst_EX (
          .in1(EX_pc_target_src_a),
          .in2(EX_imm_ext),
          .sum(EX_pc_target)
        );
  dtcore32_alu # (
                 .WIDTH(32)
               )
               dtcore32_alu_inst (
                 .control(EX_alu_control),
                 .a(EX_src_a),
                 .b(EX_src_b),
                 .y(EX_alu_result),
                 .BranchCond(EX_branch_cond)
               );

  // EX/MEM register
  always_ff @(posedge clk_i)
  begin
    if (rst_i)
    begin
      MEM_reg_wr <= 0;
      MEM_result_src <= 0;
      MEM_load_size <= 0;
      DMEM_wr_en <= 0;
      DMEM_addr <= 0;
      DMEM_wr_data <= 0;
      MEM_dest_reg <= 0;
      MEM_pc_plus_4 <= 0;
    end
    else
    begin
      MEM_reg_wr <= EX_reg_wr;
      MEM_result_src <= EX_result_src;
      MEM_load_size <= EX_load_size;
      DMEM_wr_en <= EX_mem_wr;
      DMEM_addr <= EX_alu_result;
      DMEM_wr_data <= EX_wr_data;
      MEM_dest_reg <= EX_dest_reg;
      MEM_pc_plus_4 <= EX_pc_plus_4;
    end
  end

  // Data Memory stage
  load_size_conv  load_size_conv_inst (
                    .load_size(MEM_load_size),
                    .byte_num(DMEM_addr[1:0]),
                    .rd_data(DMEM_rd_data_i),
                    .converted_data(MEM_rd_data)
                  );

  // MEM/WB register
  always_ff@(posedge clk_i)
  begin
    if(rst_i)
    begin
      WB_reg_wr <= 0;
      WB_result_src <= 0;
      WB_alu_result <= 0;
      WB_rd_data <= 0;
      WB_dest_reg <= 0;
      WB_pc_plus_4 <= 0;
    end
    else
    begin
      WB_reg_wr <= MEM_reg_wr;
      WB_result_src <= MEM_result_src;
      WB_alu_result <= DMEM_addr;
      WB_rd_data <= MEM_rd_data;
      WB_dest_reg <= MEM_dest_reg;
      WB_pc_plus_4 <= MEM_pc_plus_4;
    end
  end

  // Writeback stage
  mux3to1 # (
            .WIDTH(32)
          )
          mux3to1_inst_WB (
            .in0(WB_alu_result),
            .in1(WB_rd_data),
            .in2(WB_pc_plus_4),
            .sel(WB_result_src),
            .out(WB_result)
          );

  // Hazard Unit
  dtcore32_hazunit  dtcore32_hazunit_inst (
                      .Rs1E(EX_src_reg_1),
                      .Rs2E(EX_src_reg_2),
                      .RdM(MEM_dest_reg),
                      .RdW(WB_dest_reg),
                      .RegWriteM(MEM_reg_wr),
                      .RegWriteW(WB_reg_wr),
                      .ResultSrcEb0(EX_result_src[0]),
                      .Rs1D(ID_src_reg_1),
                      .Rs2D(ID_src_reg_2),
                      .RdE(EX_dest_reg),
                      .PCSrcE(EX_pc_src),
                      .ForwardAE(EX_forward_a),
                      .ForwardBE(EX_forward_b),
                      .StallF(IF_stall),
                      .StallD(ID_stall),
                      .FlushE(EX_flush),
                      .FlushD(ID_flush)
                    );
endmodule
