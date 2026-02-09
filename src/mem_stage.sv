import riscv_pkg::*;
module mem_stage (
  // Clock & Reset
  input  logic        clk_i                 ,
  input  logic        rst_i                 ,
  // Pipeline inputs
  input  logic [31:0] mem_q_pc              ,
  input  logic        mem_q_valid           ,
  input  logic [31:0] mem_q_store_wdata     ,
  input  logic        mem_q_is_rd_write     ,
  input  logic [ 4:0] mem_q_rd_addr         ,
  input  logic        mem_q_is_csr_write    ,
  input  logic        mem_q_is_csr_read     ,
  input  logic [11:0] mem_q_csr_addr        ,
  input  logic [31:0] mem_q_csr_wdata       ,
  input  logic [31:0] mem_q_alu_csr_result  ,
  input  logic        mem_q_is_mem_read     ,
  input  logic        mem_q_is_mem_write    ,
  input  logic        mem_q_is_memsize_w    ,
  input  logic        mem_q_is_memsize_h    ,
  input  logic        mem_q_is_memsize_hu   ,
  input  logic        mem_q_is_memsize_b    ,
  input  logic        mem_q_is_memsize_bu   ,
  input  logic        mem_q_is_jal          ,
  input  logic        mem_q_is_jalr         ,
  input  logic        mem_q_is_branch       ,
  input  logic        mem_q_branch_predict  ,
  input  logic        mem_q_jump_taken      ,
  input  logic [31:0] mem_q_pc_plus_4       ,
  input  logic        mem_q_trap_valid      ,
  input  logic [31:0] mem_q_trap_pc         ,
  input  logic [31:0] mem_q_trap_mcause     ,
  // Memory interface
  input  logic [31:0] mem_rdata_i           ,
  output logic [ 3:0] mem_strb_o            ,
  output logic [31:0] mem_addr_o            ,
  output logic [31:0] mem_wdata_o           ,
  output logic        mem_wen_o             ,
  output logic        mem_valid_o           ,
  output logic        dmem_periph_req       ,
  output logic        mem_done_i            ,
  // Pipeline outputs
  output logic        mem_d_valid           ,
  output logic        mem_d_is_rd_write     ,
  output logic [ 4:0] mem_d_rd_addr         ,
  output logic [31:0] mem_d_rd_wdata        ,
  output logic        mem_d_is_csr_write    ,
  output logic        mem_d_is_csr_read     ,
  output logic [11:0] mem_d_csr_addr        ,
  output logic [31:0] mem_d_csr_wdata       ,
  output logic [31:0] mem_d_pc_plus_4       ,
  // Trap outputs
  output logic        mem_d_trap_valid      ,
  output logic [31:0] mem_d_trap_pc         ,
  output logic [31:0] mem_d_trap_mcause     ,
  output logic        mem_btaken_mispredict ,
  output logic        mem_bntaken_mispredict,
  output logic        mem_branch_mispredict
`ifdef RISCV_FORMAL
  ,
  input  logic [31:0] mem_q_next_pc         ,
  input  logic [31:0] mem_q_insn            ,
  input  logic        mem_q_intr            ,
  input  logic [31:0] mem_q_csr_rdata       ,
  input  logic [31:0] mem_q_jaddr           ,
  input  logic [31:0] mem_q_rs1_rdata       ,
  input  logic [31:0] mem_q_rs2_rdata       ,
  input  logic [ 4:0] mem_q_rs1_addr        ,
  input  logic [ 4:0] mem_q_rs2_addr        ,
  input  logic [31:0] mem_q_trap_insn       ,
  input  logic [31:0] mem_q_trap_next_pc    ,
  input  logic [ 4:0] mem_q_trap_rs1_addr   ,
  input  logic [ 4:0] mem_q_trap_rs2_addr   ,
  input  logic [ 4:0] mem_q_trap_rd_addr    ,
  input  logic [31:0] mem_q_trap_rs1_rdata  ,
  input  logic [31:0] mem_q_trap_rs2_rdata  ,
  input  logic [31:0] trap_handler_addr     ,
  // RVFI signals
  output logic [31:0] mem_d_pc              ,
  output logic [31:0] mem_d_next_pc         ,
  output logic [31:0] mem_d_insn            ,
  output logic        mem_d_intr            ,
  output logic [ 4:0] mem_d_rs1_addr        ,
  output logic [ 4:0] mem_d_rs2_addr        ,
  output logic [31:0] mem_d_rs1_rdata       ,
  output logic [31:0] mem_d_rs2_rdata       ,
  output logic [31:0] mem_d_mem_addr        ,
  output logic [ 3:0] mem_d_load_rmask      ,
  output logic [ 3:0] mem_d_store_wmask     ,
  output logic [31:0] mem_d_store_wdata     ,
  output logic [31:0] mem_d_csr_rdata       ,
  output logic [31:0] mem_d_load_rdata      ,
  output logic [31:0] mem_d_trap_insn       ,
  output logic [31:0] mem_d_trap_next_pc    ,
  output logic [ 4:0] mem_d_trap_rs1_addr   ,
  output logic [ 4:0] mem_d_trap_rs2_addr   ,
  output logic [ 4:0] mem_d_trap_rd_addr    ,
  output logic [31:0] mem_d_trap_rs1_rdata  ,
  output logic [31:0] mem_d_trap_rs2_rdata  ,
  output logic [31:0] mem_d_trap_rd_wdata
`endif
);



  logic [ 3:0] mem_rstrb        ;
  logic [ 3:0] mem_wstrb        ;
  logic [ 4:0] load_size_onehot ;
  logic [ 2:0] store_size_onehot;
  logic        mem_valid        ;
  logic   [31:0] mem_load_rdata   ;
  logic        misaligned_load  ;
  logic        misaligned_store ;
  assign mem_btaken_mispredict  = (mem_q_is_branch && !mem_q_jump_taken && mem_q_branch_predict);
  assign mem_bntaken_mispredict = (mem_q_is_branch && mem_q_jump_taken && !mem_q_branch_predict);
  assign mem_branch_mispredict  = mem_btaken_mispredict || mem_bntaken_mispredict;
  assign load_size_onehot       = !mem_q_is_mem_read ? 0 :
    {
      mem_q_is_memsize_w,
      mem_q_is_memsize_hu,
      mem_q_is_memsize_h,
      mem_q_is_memsize_bu,
      mem_q_is_memsize_b
    };
  assign store_size_onehot = !mem_q_is_mem_write ? 0 :
    {
      mem_q_is_memsize_w,
      mem_q_is_memsize_h,
      mem_q_is_memsize_b
    };

  pulse_generator pulse_generator_inst (
    .clk_i  (clk_i                         ),
    .rst_i  (rst_i                         ),
    .en_i   (dmem_periph_req && !mem_done_i),
    .pulse_o(mem_valid                     )
  );
  assign mem_valid_o = mem_valid;
  //*****************************************************************
  //
  //
  // LOAD UNIT
  //
  //
  //*****************************************************************

  load_unit load_unit_instance (
    .rdata_unformatted(mem_rdata_i),
    .addr(mem_q_alu_csr_result),
    .load_size_onehot(load_size_onehot),
    .rstrb(mem_rstrb),
    .rdata_formatted(mem_load_rdata),
    .misaligned_load(misaligned_load)
  );

  //*****************************************************************
  //
  //
  // STORE UNIT
  //
  //
  //*****************************************************************
  store_unit store_unit_instance (
    .addr(mem_q_alu_csr_result),
    .wdata_unformatted(mem_q_store_wdata),
    .store_size_onehot(store_size_onehot),
    .wdata_formatted(mem_wdata_o),
    .wstrb(mem_wstrb),
    .misaligned_store(misaligned_store)
  );

  always_comb
    begin
      // memory interface local signals
      dmem_periph_req = (mem_q_is_mem_write || mem_q_is_mem_read) && !(misaligned_load || misaligned_store);
      mem_wen_o       = mem_q_is_mem_write;
      mem_addr_o      = mem_q_alu_csr_result;
      mem_strb_o      = mem_wen_o ? mem_wstrb : mem_rstrb;

      // pipeline
      mem_d_valid        = mem_q_valid;
      mem_d_is_csr_write = mem_q_is_csr_write;
      mem_d_is_csr_read  = mem_q_is_csr_read;
      mem_d_is_rd_write  = misaligned_load ? 0 : mem_q_is_rd_write;
      mem_d_rd_addr      = mem_q_rd_addr;
      mem_d_pc_plus_4    = mem_q_pc_plus_4;

      if (mem_q_is_jalr | mem_q_is_jal)  // is a jal or jalr
        mem_d_rd_wdata = mem_q_pc_plus_4;
      else if (mem_q_is_mem_read)  // is a load instruction
        mem_d_rd_wdata = mem_load_rdata;
      else  // else
        mem_d_rd_wdata = mem_q_alu_csr_result;

      mem_d_csr_addr  = mem_q_csr_addr;
      mem_d_csr_wdata = mem_q_csr_wdata;
      // traps
      if (mem_q_trap_valid)
        begin
          mem_d_trap_valid  = 1;
          mem_d_trap_mcause = mem_q_trap_mcause;
          mem_d_trap_pc     = mem_q_trap_pc;
        end
      else if (misaligned_store)
        begin
          mem_d_trap_valid  = 1;
          mem_d_trap_mcause = {1'b0, TRAP_CODE_STORE_ADDR_MISALIGNED};
          mem_d_trap_pc     = mem_q_pc;

        end
      else if (misaligned_load)
        begin
          mem_d_trap_valid  = 1;
          mem_d_trap_mcause = {1'b0, TRAP_CODE_LOAD_ADDR_MISALIGNED};
          mem_d_trap_pc     = mem_q_pc;
        end
      else
        begin
          mem_d_trap_valid  = 0;
          mem_d_trap_mcause = 0;
          mem_d_trap_pc     = 0;
        end
    end

`ifdef RISCV_FORMAL
  always_comb
  begin
    // rvfi
    mem_d_pc      = mem_q_pc;
    // next pc changes on a branch mispredict
    mem_d_next_pc = mem_q_trap_valid ? trap_handler_addr :
      mem_q_jump_taken ? mem_q_jaddr :
      mem_q_pc_plus_4;
    mem_d_insn        = mem_q_insn;
    mem_d_intr        = mem_q_intr;
    mem_d_rs1_addr    = mem_q_rs1_addr;
    mem_d_rs2_addr    = mem_q_rs2_addr;
    mem_d_rs1_rdata   = mem_q_rs1_rdata;
    mem_d_rs2_rdata   = mem_q_rs2_rdata;
    // mem addresses are always word aligned
    mem_d_mem_addr    = mem_addr_o & ~32'h3;
    mem_d_load_rmask  = mem_rstrb;
    mem_d_store_wmask = mem_wstrb;
    mem_d_store_wdata = mem_wdata_o;
    mem_d_csr_rdata   = mem_q_csr_rdata;
    mem_d_load_rdata  = mem_rdata_i;
    // trap
    // if trap comes from previous stage save it instead
    if (mem_q_trap_valid) begin
      mem_d_trap_insn      = mem_q_trap_insn;
      mem_d_trap_next_pc   = mem_q_trap_next_pc;
      mem_d_trap_rs1_addr  = mem_q_trap_rs1_addr;
      mem_d_trap_rs2_addr  = mem_q_trap_rs2_addr;
      mem_d_trap_rd_addr   = mem_q_trap_rd_addr;
      mem_d_trap_rs1_rdata = mem_q_trap_rs1_rdata;
      mem_d_trap_rs2_rdata = mem_q_trap_rs2_rdata;
      mem_d_trap_rd_wdata  = 0;
    end else begin
      mem_d_trap_insn      = mem_q_insn;
      mem_d_trap_next_pc   = mem_q_next_pc;
      mem_d_trap_rs1_addr  = mem_q_rs1_addr;
      mem_d_trap_rs2_addr  = mem_q_rs2_addr;
      mem_d_trap_rd_addr   = mem_q_rd_addr;
      mem_d_trap_rs1_rdata = mem_q_rs1_rdata;
      mem_d_trap_rs2_rdata = mem_q_rs2_rdata;
      mem_d_trap_rd_wdata  = 0;
    end

  end
`endif

endmodule