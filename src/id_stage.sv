import riscv_pkg::*;
module id_stage (
  input  logic [                       31:0] id_q_insn           ,
  input  logic                               id_forward_rs1      ,
  input  logic                               id_forward_rs2      ,
  input  logic                               id_q_intr           ,
  input  logic [                       31:0] id_q_pc             ,
  input  logic                               id_predict_btaken   ,
  input  logic [                        5:0] id_pht_idx          ,
  input  logic                               id_q_valid          ,
  input  logic [                       31:0] id_q_pc_plus_4      ,
  input  logic [                       31:0] wb_rd_wdata         ,
  input  logic [                       31:0] regfile_rs1_rdata   ,
  input  logic [                       31:0] regfile_rs2_rdata   ,
  input  logic [                       31:0] csrfile_rdata       ,
  output logic [                       31:0] id_branch_addr      ,
  output logic                               id_d_is_branch      ,
  output logic                               id_d_is_jump        ,
  output logic                               id_d_is_jal         ,
  output logic                               id_d_is_jalr        ,
  output logic                               id_d_branch_predict ,
  output logic [                        5:0] id_d_pht_idx        ,
  output logic                               id_d_is_csr_write   ,
  output logic                               id_d_is_csr_read    ,
  output logic                               id_d_csr_op_rw      ,
  output logic                               id_d_csr_op_clear   ,
  output logic                               id_d_csr_op_set     ,
  output logic                               id_d_is_rd_write    ,
  output logic                               id_d_is_rs1_read    ,
  output logic                               id_d_is_rs2_read    ,
  output logic                               id_d_is_mem_write   ,
  output logic                               id_d_is_mem_read    ,
  output logic                               id_d_is_memsize_b   ,
  output logic                               id_d_is_memsize_bu  ,
  output logic                               id_d_is_memsize_h   ,
  output logic                               id_d_is_memsize_hu  ,
  output logic                               id_d_is_memsize_w   ,
  output logic                               id_d_valid          ,
  output logic [                       31:0] id_d_pc             ,
  output logic [                       31:0] id_d_pc_plus_4      ,
  output logic [                        4:0] id_d_rs1_addr       ,
  output logic [                        4:0] id_d_rs2_addr       ,
  output logic [                        4:0] id_d_rd_addr        ,
  output logic [                       31:0] id_d_rs1_rdata      ,
  output logic [                       31:0] id_d_rs2_rdata      ,
  output logic [                       31:0] id_d_imm_ext        ,
  output logic [                       11:0] id_d_csr_addr       ,
  output logic [                       31:0] id_d_csr_rdata      ,
  output logic [       ALU_CTRL_T_WIDTH-1:0] id_d_alu_control    ,
  output logic [      ALU_A_SEL_T_WIDTH-1:0] id_d_alu_a_sel      ,
  output logic [      ALU_B_SEL_T_WIDTH-1:0] id_d_alu_b_sel      ,
  output logic [     PC_ALU_SEL_T_WIDTH-1:0] id_d_pc_alu_sel     ,
  output logic [CSR_BITMASK_SEL_T_WIDTH-1:0] id_d_csr_bitmask_sel,
  output logic                               id_d_trap_valid     ,
  output logic [                       31:0] id_d_trap_pc        ,
  output logic [                       31:0] id_d_trap_mcause
`ifdef RISCV_FORMAL
  ,
  output logic [                       31:0] id_d_insn           ,
  output logic                               id_d_intr           ,
  output logic [                       31:0] id_d_trap_insn      ,
  output logic [                       31:0] id_d_trap_next_pc   ,
  output logic [                        4:0] id_d_trap_rs1_addr  ,
  output logic [                        4:0] id_d_trap_rs2_addr  ,
  output logic [                        4:0] id_d_trap_rd_addr   ,
  output logic [                       31:0] id_d_trap_rs1_rdata ,
  output logic [                       31:0] id_d_trap_rs2_rdata ,
  output logic [                       31:0] id_d_trap_rd_wdata
`endif
);

  logic [                        6:0] id_op             ;
  logic [                        2:0] id_funct3         ;
  logic [                        6:0] id_funct7         ;
  logic [                       11:0] id_funct12        ;
  logic [                        4:0] id_rs1_addr       ;
  logic [                        4:0] id_rd_addr        ;
  logic                               ecall_m_trap      ;
  logic                               illegal_instr_trap;
  logic                               breakpoint_trap   ;
  logic                               is_rd_write       ;
  logic                               is_rs1_read       ;
  logic                               is_rs2_read       ;
  logic [         ALU_OP_T_WIDTH-1:0] alu_op            ;
  logic                               is_branch         ;
  logic                               is_jump           ;
  logic                               is_jal            ;
  logic                               is_jalr           ;
  logic                               is_csr_write      ;
  logic                               is_csr_read       ;
  logic                               csr_op_rw         ;
  logic                               csr_op_clear      ;
  logic                               csr_op_set        ;
  logic                               is_mem_write      ;
  logic                               is_mem_read       ;
  logic                               is_memsize_b      ;
  logic                               is_memsize_bu     ;
  logic                               is_memsize_h      ;
  logic                               is_memsize_hu     ;
  logic                               is_memsize_w      ;
  logic [     IMM_EXT_OP_T_WIDTH-1:0] imm_ext_op        ;
  logic [      ALU_A_SEL_T_WIDTH-1:0] alu_a_src         ;
  logic [      ALU_B_SEL_T_WIDTH-1:0] alu_b_src         ;
  logic [     PC_ALU_SEL_T_WIDTH-1:0] pc_alu_src        ;
  logic [CSR_BITMASK_SEL_T_WIDTH-1:0] csr_bitmask_sel   ;


  logic                        id_rtype_alt;
  logic                        id_itype_alt;
  logic [ALU_CTRL_T_WIDTH-1:0] alu_control ;

  logic [ 2:0] id_imm_ext_op;
  logic [31:0] id_imm_ext   ;

  // ID-stage internal signals (single declaration block)

  logic [       ALU_CTRL_T_WIDTH-1:0] id_alu_control    ;
  logic [      ALU_A_SEL_T_WIDTH-1:0] id_alu_a_sel      ;
  logic [      ALU_B_SEL_T_WIDTH-1:0] id_alu_b_sel      ;
  logic [     PC_ALU_SEL_T_WIDTH-1:0] id_pc_alu_sel     ;
  logic [CSR_BITMASK_SEL_T_WIDTH-1:0] id_csr_bitmask_sel;

  logic id_illegal_instr_trap;
  logic id_ecall_m_trap      ;
  logic id_breakpoint_trap   ;

  logic id_is_branch;
  logic id_is_jump  ;
  logic id_is_jal   ;
  logic id_is_jalr  ;

  logic id_is_csr_write;
  logic id_is_csr_read ;
  logic id_csr_op_rw   ;
  logic id_csr_op_clear;
  logic id_csr_op_set  ;

  logic id_is_rd_write;
  logic id_is_rs1_read;
  logic id_is_rs2_read;

  logic id_is_mem_write;
  logic id_is_mem_read ;

  logic id_is_memsize_b ;
  logic id_is_memsize_bu;
  logic id_is_memsize_h ;
  logic id_is_memsize_hu;
  logic id_is_memsize_w ;

// decoded instruction fields
  logic        id_funct7b5;
  logic [ 4:0] id_rs2_addr;
  logic [11:0] id_csr_addr;



  maindec maindec_inst (
    .id_op             (id_op             ),
    .id_funct3         (id_funct3         ),
    .id_funct7         (id_funct7         ),
    .id_funct12        (id_funct12        ),
    .id_rs1_addr       (id_rs1_addr       ),
    .id_rd_addr        (id_rd_addr        ),
    .ecall_m_trap      (ecall_m_trap      ),
    .illegal_instr_trap(illegal_instr_trap),
    .breakpoint_trap   (breakpoint_trap   ),
    .is_rd_write       (is_rd_write       ),
    .is_rs1_read       (is_rs1_read       ),
    .is_rs2_read       (is_rs2_read       ),
    .alu_op            (alu_op            ),
    .is_branch         (is_branch         ),
    .is_jump           (is_jump           ),
    .is_jal            (is_jal            ),
    .is_jalr           (is_jalr           ),
    .is_csr_write      (is_csr_write      ),
    .is_csr_read       (is_csr_read       ),
    .csr_op_rw         (csr_op_rw         ),
    .csr_op_clear      (csr_op_clear      ),
    .csr_op_set        (csr_op_set        ),
    .is_mem_write      (is_mem_write      ),
    .is_mem_read       (is_mem_read       ),
    .is_memsize_b      (is_memsize_b      ),
    .is_memsize_bu     (is_memsize_bu     ),
    .is_memsize_h      (is_memsize_h      ),
    .is_memsize_hu     (is_memsize_hu     ),
    .is_memsize_w      (is_memsize_w      ),
    .imm_ext_op        (imm_ext_op        ),
    .alu_a_src         (alu_a_src         ),
    .alu_b_src         (alu_b_src         ),
    .pc_alu_src        (pc_alu_src        ),
    .csr_bitmask_sel   (csr_bitmask_sel   )
  );


  aludec aludec_inst (
    .id_funct3   (id_funct3   ),
    .id_rtype_alt(id_rtype_alt),
    .id_itype_alt(id_itype_alt),
    .alu_op      (alu_op      ),
    .alu_control (alu_control )
  );

  extend ext_inst (
    .id_q_insn    (id_q_insn    ),
    .id_imm_ext_op(id_imm_ext_op),
    .id_imm_ext   (id_imm_ext   )
  );

  assign id_alu_control        = alu_control;
  assign id_imm_ext_op         = imm_ext_op;
  assign id_alu_a_sel          = alu_a_src;
  assign id_alu_b_sel          = alu_b_src;
  assign id_pc_alu_sel         = pc_alu_src;
  assign id_csr_bitmask_sel    = csr_bitmask_sel;
  assign id_illegal_instr_trap = illegal_instr_trap;
  assign id_ecall_m_trap       = ecall_m_trap;
  assign id_breakpoint_trap    = breakpoint_trap;

  assign id_is_branch     = is_branch;
  assign id_is_jump       = is_jump;
  assign id_is_jal        = is_jal;
  assign id_is_jalr       = is_jalr;
  assign id_is_csr_write  = is_csr_write;
  assign id_is_csr_read   = is_csr_read;
  assign id_csr_op_rw     = csr_op_rw;
  assign id_csr_op_clear  = csr_op_clear;
  assign id_csr_op_set    = csr_op_set;
  assign id_is_rd_write   = (|id_rd_addr) ? is_rd_write : 0;
  assign id_is_rs1_read   = is_rs1_read;
  assign id_is_rs2_read   = is_rs2_read;
  assign id_is_mem_write  = is_mem_write;
  assign id_is_mem_read   = is_mem_read;
  assign id_is_memsize_b  = is_memsize_b;
  assign id_is_memsize_bu = is_memsize_bu;
  assign id_is_memsize_h  = is_memsize_h;
  assign id_is_memsize_hu = is_memsize_hu;
  assign id_is_memsize_w  = is_memsize_w;

  // assign signals propagating to the next stage
  always @(*)
  begin
    id_op          = id_q_insn[6:0];
    id_funct3      = id_q_insn[14:12];
    id_funct7b5    = id_q_insn[30];
    id_funct7      = id_q_insn[31:25];
    id_funct12     = id_q_insn[31:20];
    id_rtype_alt   = id_op[5] & id_funct7b5;
    id_itype_alt   = ~id_op[5] & id_funct7b5;
    id_rs1_addr    = id_is_rs1_read ? id_q_insn[19:15] : 0;
    id_rs2_addr    = id_is_rs2_read ? id_q_insn[24:20] : 0;
    id_rd_addr     = id_q_insn[11:7];
    id_csr_addr    = id_q_insn[31:20];
    // Branch and jump
    id_branch_addr = id_q_pc +
      {{20{id_q_insn[31]}}, id_q_insn[7], id_q_insn[30:25], id_q_insn[11:8], 1'b0};
    id_d_is_branch      = id_is_branch;
    id_d_is_jump        = id_is_jump;
    id_d_is_jal         = id_is_jal;
    id_d_is_jalr        = id_is_jalr;
    id_d_branch_predict = id_predict_btaken;
    id_d_pht_idx        = id_pht_idx;

    // CSR operations
    id_d_is_csr_write = id_is_csr_write;
    id_d_is_csr_read  = id_is_csr_read;
    id_d_csr_op_rw    = id_csr_op_rw;
    id_d_csr_op_clear = id_csr_op_clear;
    id_d_csr_op_set   = id_csr_op_set;

    // Register reads/writes
    id_d_is_rd_write = id_is_rd_write;
    id_d_is_rs1_read = id_is_rs1_read;
    id_d_is_rs2_read = id_is_rs2_read;

    // Memory access
    id_d_is_mem_write = id_is_mem_write;
    id_d_is_mem_read  = id_is_mem_read;

    // Memory size indicators
    id_d_is_memsize_b  = id_is_memsize_b;
    id_d_is_memsize_bu = id_is_memsize_bu;
    id_d_is_memsize_h  = id_is_memsize_h;
    id_d_is_memsize_hu = id_is_memsize_hu;
    id_d_is_memsize_w  = id_is_memsize_w;

    //
    id_d_valid           = id_q_valid;
    id_d_pc              = id_q_pc;
    id_d_pc_plus_4       = id_q_pc_plus_4;
    id_d_rs1_addr        = id_rs1_addr;
    id_d_rs2_addr        = id_rs2_addr;
    id_d_rd_addr         = id_rd_addr;
    id_d_rs1_rdata       = id_forward_rs1 ? wb_rd_wdata : regfile_rs1_rdata;
    id_d_rs2_rdata       = id_forward_rs2 ? wb_rd_wdata : regfile_rs2_rdata;
    id_d_imm_ext         = id_imm_ext;
    id_d_csr_addr        = id_csr_addr;
    id_d_csr_rdata       = csrfile_rdata;
    id_d_alu_control     = id_alu_control;
    id_d_alu_a_sel       = id_alu_a_sel;
    id_d_alu_b_sel       = id_alu_b_sel;
    id_d_pc_alu_sel      = id_pc_alu_sel;
    id_d_csr_bitmask_sel = id_csr_bitmask_sel;
    // trap info
    if (id_ecall_m_trap) begin
      id_d_trap_valid  = 1;
      id_d_trap_pc     = id_q_pc;
      id_d_trap_mcause = {1'd0, TRAP_CODE_ECALL_M_MODE};
    end
    else if (id_breakpoint_trap) begin
      id_d_trap_valid  = 1;
      id_d_trap_pc     = id_q_pc;
      id_d_trap_mcause = {1'd0, TRAP_CODE_BREAKPOINT};
    end
    else if (id_illegal_instr_trap) begin
      id_d_trap_valid  = 1;
      id_d_trap_pc     = id_q_pc;
      id_d_trap_mcause = {1'd0, TRAP_CODE_ILLEGAL_INSTR};
    end
    else begin
      id_d_trap_valid  = 0;
      id_d_trap_mcause = 0;
      id_d_trap_pc     = 0;
    end

  end

`ifdef RISCV_FORMAL
  always @(*)
  begin
    // rvfi metadata
    id_d_insn           = id_q_insn;
    id_d_intr           = id_q_intr;
    // trap info for rvfi
    id_d_trap_insn      = id_q_insn;
    //id_d_trap_pc = id_q_pc;
    id_d_trap_next_pc   = 0;
    id_d_trap_rs1_addr  = 0;
    id_d_trap_rs2_addr  = 0;
    id_d_trap_rd_addr   = 0;
    id_d_trap_rs1_rdata = 0;
    id_d_trap_rs2_rdata = 0;
    id_d_trap_rd_wdata  = 0;
  end
`endif
endmodule