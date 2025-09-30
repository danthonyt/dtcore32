//===========================================================
// Project    : RISC-V CPU
// File       : dtcore32.v
// Module     : dtcore32
// Description: Top-level CPU core module implementing a 32-bit
//              RISC-V pipeline. Interfaces with instruction memory,
//              and a unified data interface for memory-mapped
//              data memory or peripherals. Handles CSR, traps, and
//              optional formal verification signals (`RISCV_FORMAL`).
//
// Inputs:
//   clk_i                - System clock
//   rst_i                - Synchronous reset
//   imem_rdata_i         - Instruction memory read data
//   mem_rdata_i          - Read data from data memory or peripheral
//   mem_done_i           - Transaction completion from data memory or peripheral
//   (RISCV_FORMAL) rvfi signals - Optional outputs for formal verification
//
// Outputs:
//   imem_addr_o          - Instruction memory address
//   mem_valid_o          - Valid signal for data memory or peripheral transaction
//   mem_wen_o            - Write enable for data memory or peripheral
//   mem_addr_o           - Address for data memory or peripheral
//   mem_wdata_o          - Write data for data memory or peripheral
//   mem_strb_o           - Byte-enable strobes for write operations
//   (RISCV_FORMAL) rvfi signals - Optional formal verification outputs
//
// Notes:
//   - Integrates instruction fetch, decode, execute, memory, and write-back stages.
//   - Unified `mem_*` interface can access both data memory and memory-mapped peripherals.
//   - Optional RISCV_FORMAL signals allow formal verification of CPU behavior.
//   - Designed to interface with external CSR module and trap handling logic.
//
// Author     : David Torres
// Date       : 2025-09-16
//===========================================================

// Optional: conditional compilation flag
  define RISCV_FORMAL
module dtcore32 (
  input             clk_i                  ,
  input             rst_i                  ,
`ifdef RISCV_FORMAL
  output reg        rvfi_valid             ,
  output reg [63:0] rvfi_order             ,
  output reg [31:0] rvfi_insn              ,
  output reg        rvfi_trap              ,
  output reg        rvfi_halt              ,
  output reg        rvfi_intr              ,
  output reg [ 1:0] rvfi_mode              ,
  output reg [ 1:0] rvfi_ixl               ,
  output reg [ 4:0] rvfi_rs1_addr          ,
  output reg [ 4:0] rvfi_rs2_addr          ,
  output reg [31:0] rvfi_rs1_rdata         ,
  output reg [31:0] rvfi_rs2_rdata         ,
  output reg [ 4:0] rvfi_rd_addr           ,
  output reg [31:0] rvfi_rd_wdata          ,
  output reg [31:0] rvfi_pc_rdata          ,
  output reg [31:0] rvfi_pc_wdata          ,
  output reg [31:0] rvfi_mem_addr          ,
  output reg [ 3:0] rvfi_mem_rmask         ,
  output reg [ 3:0] rvfi_mem_wmask         ,
  output reg [31:0] rvfi_mem_rdata         ,
  output reg [31:0] rvfi_mem_wdata         ,
  output reg [63:0] rvfi_csr_mcycle_rmask  ,
  output reg [63:0] rvfi_csr_mcycle_wmask  ,
  output reg [63:0] rvfi_csr_mcycle_rdata  ,
  output reg [63:0] rvfi_csr_mcycle_wdata  ,
  output reg [63:0] rvfi_csr_minstret_rmask,
  output reg [63:0] rvfi_csr_minstret_wmask,
  output reg [63:0] rvfi_csr_minstret_rdata,
  output reg [63:0] rvfi_csr_minstret_wdata,
  output reg [31:0] rvfi_csr_mcause_rmask  ,
  output reg [31:0] rvfi_csr_mcause_wmask  ,
  output reg [31:0] rvfi_csr_mcause_rdata  ,
  output reg [31:0] rvfi_csr_mcause_wdata  ,
  output reg [31:0] rvfi_csr_mepc_rmask    ,
  output reg [31:0] rvfi_csr_mepc_wmask    ,
  output reg [31:0] rvfi_csr_mepc_rdata    ,
  output reg [31:0] rvfi_csr_mepc_wdata    ,
  output reg [31:0] rvfi_csr_mtvec_rmask   ,
  output reg [31:0] rvfi_csr_mtvec_wmask   ,
  output reg [31:0] rvfi_csr_mtvec_rdata   ,
  output reg [31:0] rvfi_csr_mtvec_wdata   ,
`endif
  // to instruction memory interface
  input      [31:0] imem_rdata_i           ,
  output reg [31:0] imem_addr_o            ,
  // to data memory and peripheral interface
  input      [31:0] mem_rdata_i            ,
  input             mem_done_i             ,
  output         mem_valid_o            ,
  output reg        mem_wen_o              ,
  output reg [31:0] mem_addr_o             ,
  output reg [31:0] mem_wdata_o            ,
  output reg [ 3:0] mem_strb_o
);




//-------------------------------
// Widths for pseudo-types
//-------------------------------
  localparam FWD_SEL_T_WIDTH         = 2;
  localparam IMM_EXT_OP_T_WIDTH      = 3;
  localparam ALU_CTRL_T_WIDTH        = 4;
  localparam ALU_A_SEL_T_WIDTH       = 2;
  localparam ALU_B_SEL_T_WIDTH       = 1;
  localparam ALU_OP_T_WIDTH          = 2;
  localparam PC_ALU_SEL_T_WIDTH      = 1;
  localparam CSR_BITMASK_SEL_T_WIDTH = 1;


//-------------------------------
// ALU Control Signals
//-------------------------------
  localparam [3:0] ADD_ALU_CONTROL       = 4'h0;
  localparam [3:0] SUB_ALU_CONTROL       = 4'h1;
  localparam [3:0] AND_ALU_CONTROL       = 4'h2;
  localparam [3:0] OR_ALU_CONTROL        = 4'h3;
  localparam [3:0] L_SHIFT_ALU_CONTROL   = 4'h4;
  localparam [3:0] LT_ALU_CONTROL        = 4'h5;
  localparam [3:0] LTU_ALU_CONTROL       = 4'h6;
  localparam [3:0] XOR_ALU_CONTROL       = 4'h7;
  localparam [3:0] R_SHIFT_A_ALU_CONTROL = 4'h8;
  localparam [3:0] R_SHIFT_L_ALU_CONTROL = 4'h9;
  localparam [3:0] GE_ALU_CONTROL        = 4'hA;
  localparam [3:0] GEU_ALU_CONTROL       = 4'hB;
  localparam [3:0] NE_ALU_CONTROL        = 4'hC;
  localparam [3:0] JALR_ALU_CONTROL      = 4'hD;

//-------------------------------
// Forwarding select
//-------------------------------
  localparam [1:0] NO_FORWARD_SEL         = 2'h0;
  localparam [1:0] FORWARD_SEL_MEM_RESULT = 2'h1;
  localparam [1:0] FORWARD_SEL_WB_RESULT  = 2'h2;

//-------------------------------
// Immediate type
//-------------------------------
  localparam [2:0]
    I_ALU_TYPE     = 3'b000,
    S_TYPE         = 3'b001,
    B_TYPE         = 3'b010,
    J_TYPE         = 3'b011,
    I_SHIFT_TYPE   = 3'b100,
    U_TYPE         = 3'b101,
    CSR_TYPE       = 3'b110;

//-------------------------------
// ALU A select
//-------------------------------
  localparam [1:0] ALU_A_SEL_REG_DATA = 2'b00;
  localparam [1:0] ALU_A_SEL_ZERO     = 2'b01;
  localparam [1:0] ALU_A_SEL_PC       = 2'b10;

//-------------------------------
// ALU B select
//-------------------------------
  localparam ALU_B_SEL_REG_DATA = 1'b0;
  localparam ALU_B_SEL_IMM      = 1'b1;

//-------------------------------
// ALU Operation type
//-------------------------------
  localparam [1:0]
    ALU_OP_ILOAD_S_U_TYPE     = 2'b00,
    ALU_OP_B_TYPE             = 2'b01,
    ALU_OP_IALU_ISHIFT_R_TYPE = 2'b10,
    ALU_OP_JALR               = 2'b11;


//-------------------------------
// PC ALU select
//-------------------------------
  localparam PC_ALU_SEL_PC       = 1'b0;
  localparam PC_ALU_SEL_REG_DATA = 1'b1;

//-------------------------------
// CSR bitmask select
//-------------------------------
  localparam CSR_BITMASK_SEL_REG_DATA = 1'b0;
  localparam CSR_BITMASK_SEL_IMM      = 1'b1;

//-------------------------------
// Opcodes
//-------------------------------
  localparam [6:0] OPCODE_LOAD         = 7'b0000011;
  localparam [6:0] OPCODE_STORE        = 7'b0100011;
  localparam [6:0] OPCODE_R_TYPE       = 7'b0110011;
  localparam [6:0] OPCODE_B_TYPE       = 7'b1100011;
  localparam [6:0] OPCODE_I_TYPE       = 7'b0010011;
  localparam [6:0] OPCODE_JAL          = 7'b1101111;
  localparam [6:0] OPCODE_U_TYPE_LUI   = 7'b0110111;
  localparam [6:0] OPCODE_U_TYPE_AUIPC = 7'b0010111;
  localparam [6:0] OPCODE_JALR         = 7'b1100111;
  localparam [6:0] OPCODE_SYSCALL_CSR  = 7'b1110011;

//-------------------------------
// Funct3 codes
//-------------------------------
  localparam [2:0] FUNCT3_LB  = 3'b000;
  localparam [2:0] FUNCT3_LH  = 3'b001;
  localparam [2:0] FUNCT3_LW  = 3'b010;
  localparam [2:0] FUNCT3_LBU = 3'b100;
  localparam [2:0] FUNCT3_LHU = 3'b101;

  localparam [2:0] FUNCT3_SB = 3'b000;
  localparam [2:0] FUNCT3_SH = 3'b001;
  localparam [2:0] FUNCT3_SW = 3'b010;

  localparam [2:0] FUNCT3_BEQ  = 3'b000;
  localparam [2:0] FUNCT3_BNE  = 3'b001;
  localparam [2:0] FUNCT3_BLT  = 3'b100;
  localparam [2:0] FUNCT3_BGE  = 3'b101;
  localparam [2:0] FUNCT3_BLTU = 3'b110;
  localparam [2:0] FUNCT3_BGEU = 3'b111;

  localparam [2:0] FUNCT3_ADD        = 3'b000;
  localparam [2:0] FUNCT3_SUB        = 3'b000;
  localparam [2:0] FUNCT3_SLL        = 3'b001;
  localparam [2:0] FUNCT3_SLT        = 3'b010;
  localparam [2:0] FUNCT3_SLTU_SLTIU = 3'b011;
  localparam [2:0] FUNCT3_XOR        = 3'b100;
  localparam [2:0] FUNCT3_SRA        = 3'b101;
  localparam [2:0] FUNCT3_SRL        = 3'b101;
  localparam [2:0] FUNCT3_SRLI       = 3'b101;
  localparam [2:0] FUNCT3_SRAI       = 3'b101;
  localparam [2:0] FUNCT3_SLLI       = 3'b001;
  localparam [2:0] FUNCT3_OR         = 3'b110;
  localparam [2:0] FUNCT3_AND        = 3'b111;

  localparam [2:0] FUNCT3_ECALL_EBREAK = 3'b000;
  localparam [2:0] FUNCT3_CSRRW        = 3'b001;
  localparam [2:0] FUNCT3_CSRRS        = 3'b010;
  localparam [2:0] FUNCT3_CSRRC        = 3'b011;
  localparam [2:0] FUNCT3_CSRRWI       = 3'b101;
  localparam [2:0] FUNCT3_CSRRSI       = 3'b110;
  localparam [2:0] FUNCT3_CSRRCI       = 3'b111;

//-------------------------------
// Funct7 codes
//-------------------------------
  localparam [6:0] FUNCT7_ADD  = 7'h00;
  localparam [6:0] FUNCT7_SUB  = 7'h20;
  localparam [6:0] FUNCT7_SLL  = 7'h00;
  localparam [6:0] FUNCT7_SLT  = 7'h00;
  localparam [6:0] FUNCT7_SLTU = 7'h00;
  localparam [6:0] FUNCT7_XOR  = 7'h00;
  localparam [6:0] FUNCT7_SRL  = 7'h00;
  localparam [6:0] FUNCT7_SRA  = 7'h20;
  localparam [6:0] FUNCT7_OR   = 7'h00;
  localparam [6:0] FUNCT7_AND  = 7'h00;
  localparam [6:0] FUNCT7_SLLI = 7'h00;
  localparam [6:0] FUNCT7_SRLI = 7'h00;
  localparam [6:0] FUNCT7_SRAI = 7'h20;

//-------------------------------
// Funct12 codes
//-------------------------------
  localparam [11:0] FUNCT12_ECALL  = 12'h000;
  localparam [11:0] FUNCT12_EBREAK = 12'h001;

//-------------------------------
// Exception codes / trap codes
//-------------------------------
  localparam [30:0] TRAP_CODE_INSTR_ADDR_MISALIGNED = 31'd0 ;
  localparam [30:0] TRAP_CODE_ILLEGAL_INSTR         = 31'd2 ;
  localparam [30:0] TRAP_CODE_BREAKPOINT            = 31'd3 ;
  localparam [30:0] TRAP_CODE_LOAD_ADDR_MISALIGNED  = 31'd4 ;
  localparam [30:0] TRAP_CODE_STORE_ADDR_MISALIGNED = 31'd6 ;
  localparam [30:0] TRAP_CODE_ECALL_M_MODE          = 31'd11;

//-------------------------------
// NOP instruction
//-------------------------------
  localparam [31:0] NOP_INSTRUCTION = 32'h00000013;

//-------------------------------
// CSR Addresses
//-------------------------------
  localparam [11:0] CSR_ADDR_MSTATUS    = 12'h300;
  localparam [11:0] CSR_ADDR_MISA       = 12'h301;
  localparam [11:0] CSR_ADDR_MIE        = 12'h304;
  localparam [11:0] CSR_ADDR_MTVEC      = 12'h305;
  localparam [11:0] CSR_ADDR_MSCRATCH   = 12'h340;
  localparam [11:0] CSR_ADDR_MEPC       = 12'h341;
  localparam [11:0] CSR_ADDR_MCAUSE     = 12'h342;
  localparam [11:0] CSR_ADDR_MTVAL      = 12'h343;
  localparam [11:0] CSR_ADDR_MIP        = 12'h344;
  localparam [11:0] CSR_ADDR_MCYCLE     = 12'hB00;
  localparam [11:0] CSR_ADDR_MCYCLEH    = 12'hB80;
  localparam [11:0] CSR_ADDR_MINSTRET   = 12'hB02;
  localparam [11:0] CSR_ADDR_MINSTRETH  = 12'hB82;
  localparam [11:0] CSR_ADDR_MVENDORID  = 12'hF11;
  localparam [11:0] CSR_ADDR_MARCHID    = 12'hF12;
  localparam [11:0] CSR_ADDR_MIMPID     = 12'hF13;
  localparam [11:0] CSR_ADDR_MHARTID    = 12'hF14;
  localparam [11:0] CSR_ADDR_MCONFIGPTR = 12'hF15;
  localparam [11:0] CSR_ADDR_NO_ADDR    = 12'h000;

  localparam RESET_PC = 32'd0;


// ---------------- IF/ID PIPELINE REGISTERS ----------------
// Going in / Coming out
  reg        if_d_valid, id_q_valid;
  reg [31:0] if_d_pc, id_q_pc;
  reg [31:0] if_d_pc_plus_4, id_q_pc_plus_4;
  reg [31:0] if_d_insn, id_q_insn;
`ifdef RISCV_FORMAL
  reg if_d_intr, id_q_intr;
`endif

// ---------------- ID/EX PIPELINE REGISTERS ----------------
// Going in / Coming out
  reg        id_d_valid, ex_q_valid;
  reg [31:0] id_d_pc, ex_q_pc;
  reg [31:0] id_d_pc_plus_4, ex_q_pc_plus_4;
  reg [ 4:0] id_d_rs1_addr, ex_q_rs1_addr;
  reg [ 4:0] id_d_rs2_addr, ex_q_rs2_addr;
  reg [ 4:0] id_d_rd_addr, ex_q_rd_addr;
  reg [31:0] id_d_rs1_rdata, ex_q_rs1_rdata;
  reg [31:0] id_d_rs2_rdata, ex_q_rs2_rdata;
  reg [31:0] id_d_imm_ext, ex_q_imm_ext;
  reg [11:0] id_d_csr_addr, ex_q_csr_addr;
  reg [31:0] id_d_csr_rdata, ex_q_csr_rdata;

  reg [       ALU_CTRL_T_WIDTH-1:0] id_d_alu_control, ex_q_alu_control;
  reg [      ALU_A_SEL_T_WIDTH-1:0] id_d_alu_a_sel, ex_q_alu_a_sel;
  reg [      ALU_B_SEL_T_WIDTH-1:0] id_d_alu_b_sel, ex_q_alu_b_sel;
  reg [     PC_ALU_SEL_T_WIDTH-1:0] id_d_pc_alu_sel, ex_q_pc_alu_sel;
  reg [CSR_BITMASK_SEL_T_WIDTH-1:0] id_d_csr_bitmask_sel, ex_q_csr_bitmask_sel;

  reg id_d_is_branch, ex_q_is_branch;
  reg id_d_is_jump, ex_q_is_jump;
  reg id_d_is_csr_write, ex_q_is_csr_write;
  reg id_d_is_csr_read, ex_q_is_csr_read;
  reg id_d_is_rd_write, ex_q_is_rd_write;
  reg id_d_is_rs1_read, ex_q_is_rs1_read;
  reg id_d_is_rs2_read, ex_q_is_rs2_read;
  reg id_d_is_mem_write, ex_q_is_mem_write;
  reg id_d_is_mem_read, ex_q_is_mem_read;

  reg id_d_is_jal, ex_q_is_jal;
  reg id_d_is_jalr, ex_q_is_jalr;
  reg id_d_is_memsize_b, ex_q_is_memsize_b;
  reg id_d_is_memsize_bu, ex_q_is_memsize_bu;
  reg id_d_is_memsize_h, ex_q_is_memsize_h;
  reg id_d_is_memsize_hu, ex_q_is_memsize_hu;
  reg id_d_is_memsize_w, ex_q_is_memsize_w;

  reg id_d_csr_op_rw, ex_q_csr_op_rw;
  reg id_d_csr_op_clear, ex_q_csr_op_clear;
  reg id_d_csr_op_set, ex_q_csr_op_set;

  reg       id_d_branch_predict, ex_q_branch_predict;
  reg [5:0] id_d_pht_idx, ex_q_pht_idx;

  reg        id_d_trap_valid, ex_q_trap_valid;
  reg [31:0] id_d_trap_mcause, ex_q_trap_mcause;
  reg [31:0] id_d_trap_pc, ex_q_trap_pc;

`ifdef RISCV_FORMAL
  reg [31:0] id_d_insn, ex_q_insn;
  reg        id_d_intr, ex_q_intr;
// For rvfi_trap_info, you can either flatten all fields or leave as separate regs
  reg [31:0] id_d_trap_insn,     ex_q_trap_insn;
  reg [31:0] id_d_trap_next_pc,  ex_q_trap_next_pc;
  reg [ 4:0] id_d_trap_rs1_addr, ex_q_trap_rs1_addr;
  reg [ 4:0] id_d_trap_rs2_addr, ex_q_trap_rs2_addr;
  reg [ 4:0] id_d_trap_rd_addr,  ex_q_trap_rd_addr;
  reg [31:0] id_d_trap_rs1_rdata, ex_q_trap_rs1_rdata;
  reg [31:0] id_d_trap_rs2_rdata, ex_q_trap_rs2_rdata;
  reg [31:0] id_d_trap_rd_wdata, ex_q_trap_rd_wdata;

`endif
// ---------------- EX/MEM PIPELINE REGISTERS ----------------
// Going in / Coming out
  reg        ex_d_valid,          mem_q_valid;
  reg [31:0] ex_d_pc,             mem_q_pc;
  reg [31:0] ex_d_pc_plus_4,      mem_q_pc_plus_4;
  reg [ 4:0] ex_d_rd_addr,        mem_q_rd_addr;
  reg [11:0] ex_d_csr_addr,       mem_q_csr_addr;
  reg [31:0] ex_d_csr_wdata,      mem_q_csr_wdata;

  reg [31:0] ex_d_store_wdata,    mem_q_store_wdata;
  reg [31:0] ex_d_alu_csr_result, mem_q_alu_csr_result;

  reg ex_d_is_branch,      mem_q_is_branch;
  reg ex_d_is_jump,        mem_q_is_jump;
  reg ex_d_is_csr_write,   mem_q_is_csr_write;
  reg ex_d_is_csr_read,    mem_q_is_csr_read;
  reg ex_d_is_rd_write,    mem_q_is_rd_write;
  reg ex_d_is_mem_write,   mem_q_is_mem_write;
  reg ex_d_is_mem_read,    mem_q_is_mem_read;

  reg ex_d_is_jal,         mem_q_is_jal;
  reg ex_d_is_jalr,        mem_q_is_jalr;
  reg ex_d_is_memsize_b,   mem_q_is_memsize_b;
  reg ex_d_is_memsize_bu,  mem_q_is_memsize_bu;
  reg ex_d_is_memsize_h,   mem_q_is_memsize_h;
  reg ex_d_is_memsize_hu,  mem_q_is_memsize_hu;
  reg ex_d_is_memsize_w,   mem_q_is_memsize_w;

  reg       ex_d_branch_predict, mem_q_branch_predict;
  reg [5:0] ex_d_pht_idx,        mem_q_pht_idx;

  reg        ex_d_jump_taken,     mem_q_jump_taken;
  reg [31:0] ex_d_jaddr,          mem_q_jaddr;

  reg        ex_d_trap_valid,     mem_q_trap_valid;
  reg [31:0] ex_d_trap_mcause,    mem_q_trap_mcause;
  reg [31:0] ex_d_trap_pc,        mem_q_trap_pc;

`ifdef RISCV_FORMAL
  reg [31:0] ex_d_insn,           mem_q_insn;
  reg        ex_d_intr,           mem_q_intr;
  reg [31:0] ex_d_next_pc,        mem_q_next_pc;
  reg [31:0] ex_d_csr_rdata,      mem_q_csr_rdata;
  reg [ 4:0] ex_d_rs1_addr,       mem_q_rs1_addr;
  reg [ 4:0] ex_d_rs2_addr,       mem_q_rs2_addr;
  reg [31:0] ex_d_rs1_rdata,      mem_q_rs1_rdata;
  reg [31:0] ex_d_rs2_rdata,      mem_q_rs2_rdata;
// Flattened trap_info_t inside ex_mem_t
  reg [31:0] ex_d_trap_insn,      mem_q_trap_insn;
  reg [31:0] ex_d_trap_next_pc,   mem_q_trap_next_pc;
  reg [ 4:0] ex_d_trap_rs1_addr,  mem_q_trap_rs1_addr;
  reg [ 4:0] ex_d_trap_rs2_addr,  mem_q_trap_rs2_addr;
  reg [ 4:0] ex_d_trap_rd_addr,   mem_q_trap_rd_addr;
  reg [31:0] ex_d_trap_rs1_rdata, mem_q_trap_rs1_rdata;
  reg [31:0] ex_d_trap_rs2_rdata, mem_q_trap_rs2_rdata;
  reg [31:0] ex_d_trap_rd_wdata,  mem_q_trap_rd_wdata;
`endif

// ---------------- MEM/WB PIPELINE REGISTERS ----------------
// Going in / Coming out
  reg        mem_d_valid,        wb_q_valid;
  reg [ 4:0] mem_d_rd_addr,      wb_q_rd_addr;
  reg [11:0] mem_d_csr_addr,     wb_q_csr_addr;
  reg [31:0] mem_d_csr_wdata,    wb_q_csr_wdata;
  reg [31:0] mem_d_rd_wdata,     wb_q_rd_wdata;
  reg [31:0] mem_d_pc_plus_4,    wb_q_pc_plus_4;

  reg mem_d_is_csr_write, wb_q_is_csr_write;
  reg mem_d_is_csr_read,  wb_q_is_csr_read;
  reg mem_d_is_rd_write,  wb_q_is_rd_write;

  reg        mem_d_trap_valid,   wb_q_trap_valid;
  reg [31:0] mem_d_trap_mcause,  wb_q_trap_mcause;
  reg [31:0] mem_d_trap_pc,      wb_q_trap_pc;

`ifdef RISCV_FORMAL
  reg [31:0] mem_d_pc,           wb_q_pc;
  reg [31:0] mem_d_next_pc,      wb_q_next_pc;
  reg [31:0] mem_d_insn,         wb_q_insn;
  reg        mem_d_intr,         wb_q_intr;
  reg [31:0] mem_d_csr_rdata,    wb_q_csr_rdata;
  reg [31:0] mem_d_mem_addr,     wb_q_mem_addr;
  reg [31:0] mem_d_load_rdata,   wb_q_load_rdata;
  reg [ 4:0] mem_d_rs1_addr,     wb_q_rs1_addr;
  reg [ 4:0] mem_d_rs2_addr,     wb_q_rs2_addr;
  reg [31:0] mem_d_rs1_rdata,    wb_q_rs1_rdata;
  reg [31:0] mem_d_rs2_rdata,    wb_q_rs2_rdata;
  reg [ 3:0] mem_d_load_rmask,   wb_q_load_rmask;
  reg [ 3:0] mem_d_store_wmask,  wb_q_store_wmask;
  reg [31:0] mem_d_store_wdata,  wb_q_store_wdata;
// Flattened trap_info_t inside mem_wb_t
  reg [31:0] mem_d_trap_insn,    wb_q_trap_insn;
  reg [31:0] mem_d_trap_next_pc, wb_q_trap_next_pc;
  reg [ 4:0] mem_d_trap_rs1_addr,wb_q_trap_rs1_addr;
  reg [ 4:0] mem_d_trap_rs2_addr,wb_q_trap_rs2_addr;
  reg [ 4:0] mem_d_trap_rd_addr, wb_q_trap_rd_addr;
  reg [31:0] mem_d_trap_rs1_rdata, wb_q_trap_rs1_rdata;
  reg [31:0] mem_d_trap_rs2_rdata, wb_q_trap_rs2_rdata;
  reg [31:0] mem_d_trap_rd_wdata, wb_q_trap_rd_wdata;
`endif


// ---------------- WB/RVFI PIPELINE REGISTERS ----------------
// Coming out
`ifdef RISCV_FORMAL
  reg [31:0] commit_pc_rdata  ;
  reg [31:0] commit_pc_wdata  ;
  reg [31:0] commit_insn      ;
  reg        commit_valid     ;
  reg        commit_trap_valid;
  reg        commit_intr      ;
  reg [ 4:0] commit_rs1_addr  ;
  reg [ 4:0] commit_rs2_addr  ;
  reg [ 4:0] commit_rd_addr   ;
  reg [31:0] commit_rs1_rdata ;
  reg [31:0] commit_rs2_rdata ;
  reg [31:0] commit_rd_wdata  ;
  reg [11:0] commit_csr_addr  ;
  reg [31:0] commit_csr_wdata ;
  reg [31:0] commit_csr_wmask ;
  reg [31:0] commit_csr_rdata ;
  reg [31:0] commit_csr_rmask ;
  reg [31:0] commit_mem_addr  ;
  reg [ 3:0] commit_mem_rmask ;
  reg [31:0] commit_mem_rdata ;
  reg [ 3:0] commit_mem_wmask ;
  reg [31:0] commit_mem_wdata ;

  reg [31:0] commit_trap_insn     ;
  reg [31:0] commit_trap_pc       ;
  reg [31:0] commit_trap_next_pc  ;
  reg [ 4:0] commit_trap_rs1_addr ;
  reg [ 4:0] commit_trap_rs2_addr ;
  reg [ 4:0] commit_trap_rd_addr  ;
  reg [31:0] commit_trap_rs1_rdata;
  reg [31:0] commit_trap_rs2_rdata;
  reg [31:0] commit_trap_rd_wdata ;
`endif


  wire if_id_stall;
  wire if_id_flush;

  wire id_ex_stall;
  wire id_ex_flush;

  wire ex_mem_stall;
  wire ex_mem_flush;

  wire mem_wb_stall;
  wire mem_wb_flush;

  reg [31:0] mispredict_cnt;
  reg [31:0] branch_cnt    ;
  always @(posedge clk_i) begin
    if (rst_i) begin
      mispredict_cnt <= 0;
      branch_cnt     <= 0;
    end else begin
      if (mem_branch_mispredict)
        mispredict_cnt <= mispredict_cnt + 1;
      if(mem_q_is_branch)
        branch_cnt <= branch_cnt + 1;
    end
  end
`ifdef RISCV_FORMAL

  wire [31:0] wb_csr_rmask;
  wire [31:0] wb_csr_wmask;
`endif
  // if stage signals;
  reg [31:0] next_pc          ;
  reg [31:0] trap_handler_addr;
  reg [31:0] imem_addr_q      ;
  reg        imem_rdata_valid ;
  reg        imem_buf_valid   ;
  reg [31:0] if_insn_buf      ;
  reg [31:0] if_buf_pc        ;
  // branch prediction logic
  wire [31:0] id_branch_addr   ;
  wire        id_predict_btaken;
  wire [ 5:0] id_pht_idx       ;
  // id stage signals
  wire                               id_forward_rs1       ;
  wire                               id_forward_rs2       ;
  reg  [                       11:0] id_csr_addr          ;
  reg  [                       31:0] id_imm_ext           ;
  reg  [                        4:0] id_rd_addr           ;
  wire  [       ALU_CTRL_T_WIDTH-1:0] id_alu_control       ;
  reg  [                        6:0] id_op                ;
  reg  [                        2:0] id_funct3            ;
  reg                                id_funct7b5          ;
  reg  [                        6:0] id_funct7            ;
  reg  [                       11:0] id_funct12           ;
  reg                                id_rtype_alt         ;
  reg                                id_itype_alt         ;
  wire  [     IMM_EXT_OP_T_WIDTH-1:0] id_imm_ext_op        ;
  wire  [      ALU_A_SEL_T_WIDTH-1:0] id_alu_a_sel         ;
  wire  [      ALU_B_SEL_T_WIDTH-1:0] id_alu_b_sel         ;
  wire  [     PC_ALU_SEL_T_WIDTH-1:0] id_pc_alu_sel        ;
  wire  [CSR_BITMASK_SEL_T_WIDTH-1:0] id_csr_bitmask_sel   ;
  reg  [                        4:0] id_rs1_addr          ;
  reg  [                        4:0] id_rs2_addr          ;
  wire [                       31:0] regfile_rs1_rdata    ;
  wire [                       31:0] regfile_rs2_rdata    ;
  reg  [                       31:0] csrfile_rdata        ;
  wire                               id_illegal_instr_trap;
  wire                               id_ecall_m_trap      ;
  wire                               id_breakpoint_trap   ;
  wire                               id_is_branch         ;
  wire                               id_is_jump           ;
  wire                               id_is_csr_write      ;
  wire                               id_is_csr_read       ;
  wire                               id_is_rd_write       ;
  wire                               id_is_rs1_read       ;
  wire                               id_is_rs2_read       ;
  wire                               id_is_mem_write      ;
  wire                               id_is_mem_read       ;
  wire                               id_is_jal            ;
  wire                               id_is_jalr           ;
  wire                               id_is_memsize_b      ;
  wire                               id_is_memsize_bu     ;
  wire                               id_is_memsize_h      ;
  wire                               id_is_memsize_hu     ;
  wire                               id_is_memsize_w      ;
  wire                               id_csr_op_rw         ;
  wire                               id_csr_op_clear      ;
  wire                               id_csr_op_set        ;

  // ex stage signal
  reg  [ 2:0] ex_forward_rs1_sel;
  reg  [ 2:0] ex_forward_rs2_sel;
  wire [31:0] ex_jaddr          ;
  wire        ex_jump_taken     ;
  reg  [31:0] ex_rs1_rdata      ;
  reg  [31:0] ex_rs2_rdata      ;
  reg  [31:0] ex_csr_bitmask    ;
  reg  [31:0] ex_csr_wdata      ;
  reg  [31:0] ex_src_a          ;
  reg  [31:0] ex_src_b          ;
  reg  [31:0] ex_pc_base        ;
  reg         ex_branch_cond    ;
  wire        ex_misaligned_jump;
  reg  [31:0] ex_alu_result     ;

  //mem stage
  reg         misaligned_load       ;
  reg         misaligned_store      ;
  reg  [ 3:0] mem_wstrb             ;
  reg  [ 3:0] mem_rstrb             ;
  reg         dmem_periph_req       ;
  reg  [31:0] mem_load_rdata        ;
  wire         mem_btaken_mispredict ;
  wire         mem_bntaken_mispredict;
  wire        mem_branch_mispredict ;
  // writeback stage
  reg [ 4:0] wb_rd_addr    ;
  reg [11:0] wb_csr_addr   ;
  reg [31:0] wb_rd_wdata   ;
  reg [31:0] wb_csr_wdata  ;
  reg [31:0] wb_trap_mcause;
  reg [31:0] wb_trap_pc    ;
  //*****************************************************************
  //
  //
  // INSTRUCTION FETCH STAGE
  //
  //
  //*****************************************************************

  // send read address to the instruction memory
  always @(posedge clk_i)
    begin
      if (rst_i)
        begin
          imem_addr_o      <= RESET_PC;
          imem_rdata_valid <= 0;
        end
      else if (if_id_flush) begin
        imem_addr_o      <= next_pc;
        imem_rdata_valid <= 0;
      end
      else if (!if_id_stall)
        begin
          imem_addr_o      <= next_pc;
          imem_rdata_valid <= 1;
        end
    end


  // registers imem address to stay cycle aligned with imem rdata
  // imem reads have 1 cycle latency
  always @(posedge clk_i)
    begin
      if (rst_i) begin
        imem_addr_q <= RESET_PC;
      end else begin
        imem_addr_q <= imem_addr_o;
      end
    end

  // buffer
  always @(posedge clk_i)
    begin
      if (rst_i)
        begin
          imem_buf_valid <= 0;
        end
      else if (if_id_flush) begin
        imem_buf_valid <= 0;
      end
      else if (!if_id_stall)
        begin
          imem_buf_valid <= 0;
        end
      // When entering a stall, buffer the instruction memory read data.
      // When first leaving a stall, use the buffered data instead. This
      // is to avoid losing instruction data when entering a stall.
      else if (if_id_stall && !imem_buf_valid)
        begin
          if_insn_buf    <= imem_rdata_i;
          imem_buf_valid <= 1;
          if_buf_pc      <= imem_addr_q;
        end
    end

  always @(*)
    begin
      // jump to trap handler if a trap instruction commits
      // else if a branch taken and mispredicted jump to mem.pc + 4
      // else if a branch not taken and mispredicted OR a jump instruction
      // jump to mem.jaddr
      // else if a branch taken is predicted jump to that address
      // else increment pc by 4
      next_pc = wb_q_trap_valid ? trap_handler_addr :
        mem_btaken_mispredict ? mem_q_pc_plus_4 :
        mem_bntaken_mispredict ? mem_q_jaddr :
        mem_q_jump_taken && !mem_q_is_branch ? mem_q_jaddr :
        id_predict_btaken ? id_branch_addr :
        imem_addr_o + 4;
      if_d_pc        = imem_buf_valid ? if_buf_pc : imem_addr_q;
      if_d_pc_plus_4 = if_d_pc + 4;
      if_d_insn      = imem_buf_valid ? if_insn_buf : imem_rdata_i;
      if_d_valid     = imem_rdata_valid;
    end

`ifdef RISCV_FORMAL
  reg if_intr_d ;
  reg if_intr_q ;
  reg if_intr_qq;
  always @(posedge clk_i)
    begin
      if (rst_i)
        begin
          if_intr_q  <= 0;
          if_intr_qq <= 0;
        end
      else if (if_id_flush)
        begin
          if_intr_q  <= 0;
          if_intr_qq <= 0;
        end
      else if (!if_id_stall)
        begin
          if_intr_q  <= if_intr_d;
          if_intr_qq <= if_intr_q;
        end
    end
  always @(*)
    begin
      if_d_intr = if_intr_qq;
      if_intr_d = wb_q_trap_valid;
    end
`endif
  //*****************************************************************
  //
  //
  // INSTRUCTION DECODE STAGE
  //
  //
  //*****************************************************************

  //*****************************************************************
  //
  //
  // GSHARE BRANCH PREDICTOR
  //
  //
  //*****************************************************************
  reg     [5:0] ght               ;
  reg     [1:0] pht         [0:63];
  wire    [5:0] pht_idx           ;
  integer       pht_loop_idx      ;
  assign pht_idx = id_is_branch ? id_q_pc[7:2] ^ ght : 0;
  // make a branch prediction if the instruction is a branch
  assign id_predict_btaken = id_is_branch ? pht[pht_idx][1] : 0;
  assign id_pht_idx        = pht_idx;
  always @(posedge clk_i) begin
    if (rst_i) begin
      ght <= 0;
      for (pht_loop_idx = 0; pht_loop_idx < 64; pht_loop_idx = pht_loop_idx + 1) begin
        pht[pht_loop_idx] <= 2'b01;
      end
    end else begin
      if (mem_q_is_branch) begin
        // store the actual branch result if a branch instruction is resolved
        ght <= {ght[4:0], mem_q_jump_taken};
        // update 2 bit branch predictor at index
        // saturate at 2'b00 or 2'b11
        // 2'b11 is branch strongly taken and
        // 2'b00 is branch strongly not taken
        if (mem_q_jump_taken && (pht[mem_q_pht_idx] != 2'b11)) begin
          pht[mem_q_pht_idx] <= pht[mem_q_pht_idx] + 1;
        end else if (!mem_q_jump_taken && (pht[mem_q_pht_idx] != 2'b00)) begin
          pht[mem_q_pht_idx] <= pht[mem_q_pht_idx] - 1;
        end
      end

    end
  end

  reg illegal_instr_trap;
  reg ecall_m_trap      ;
  reg breakpoint_trap   ;

  reg is_branch    ;
  reg is_jump      ;
  reg is_jal       ;
  reg is_jalr      ;
  reg is_csr_write ;
  reg is_csr_read  ;
  reg csr_op_rw    ;
  reg csr_op_clear ;
  reg csr_op_set   ;
  reg is_rd_write  ;
  reg is_rs1_read  ;
  reg is_rs2_read  ;
  reg is_mem_write ;
  reg is_mem_read  ;
  reg is_memsize_b ;
  reg is_memsize_bu;
  reg is_memsize_h ;
  reg is_memsize_hu;
  reg is_memsize_w ;


  reg [       ALU_CTRL_T_WIDTH-1:0] alu_control    ;
  reg [     IMM_EXT_OP_T_WIDTH-1:0] imm_ext_op     ;
  reg [      ALU_A_SEL_T_WIDTH-1:0] alu_a_src      ;
  reg [      ALU_B_SEL_T_WIDTH-1:0] alu_b_src      ;
  reg [     PC_ALU_SEL_T_WIDTH-1:0] pc_alu_src     ;
  reg [CSR_BITMASK_SEL_T_WIDTH-1:0] csr_bitmask_sel;

  reg  [ALU_OP_T_WIDTH-1:0] alu_op                ;
  wire                      is_itype              ;
  wire                      is_rtype              ;
  wire                      is_SRAI_funct3        ;
  wire                      is_SRA_or_SUB_funct3  ;
  wire                      is_SLLI_or_SRLI_funct3;
  wire                      is_shift_itype        ;
  wire                      is_unknown_rtype      ;
  wire                      is_unknown_itype      ;

  assign is_itype               = (id_op == OPCODE_I_TYPE);
  assign is_rtype               = (id_op == OPCODE_R_TYPE);
  assign is_SRAI_funct3         = (id_funct3 == FUNCT3_SRAI);
  assign is_SRA_or_SUB_funct3   = ((id_funct3 == FUNCT3_SRA) || (id_funct3 == FUNCT3_SUB));
  assign is_SLLI_or_SRLI_funct3 = ((id_funct3 == FUNCT3_SLLI) || (id_funct3 == FUNCT3_SRLI));
  assign is_shift_itype         = is_SLLI_or_SRLI_funct3 | is_SRAI_funct3;
  assign is_unknown_rtype       = is_rtype
    & (id_funct7 != 7'h00)
    & ~((id_funct7 == 7'h20) & is_SRA_or_SUB_funct3);
  assign is_unknown_itype = is_itype
    & is_shift_itype
    & ~(is_SLLI_or_SRLI_funct3 & (id_funct7 == 7'h00))
    & ~(is_SRAI_funct3 & (id_funct7 == 7'h20));


  // Decode the control signals for the specific instruction
  always @(*) begin
    ecall_m_trap       = 0;
    illegal_instr_trap = 0;
    breakpoint_trap    = 0;
    // valid registers
    is_rd_write        = 0;
    is_rs1_read        = 0;
    is_rs2_read        = 0;
    // mux select signals
    alu_op             = 0;
    // control signals
    is_branch          = 0;
    is_jump            = 0;
    is_jal             = 0;
    is_jalr            = 0;
    is_csr_write       = 0;
    is_csr_read        = 0;
    csr_op_rw          = 0;
    csr_op_clear       = 0;
    csr_op_set         = 0;
    is_mem_write       = 0;
    is_mem_read        = 0;
    is_memsize_b       = 0;
    is_memsize_bu      = 0;
    is_memsize_h       = 0;
    is_memsize_hu      = 0;
    is_memsize_w       = 0;
    // sources
    imm_ext_op         = 0;
    alu_a_src          = 0;
    alu_b_src          = 0;
    pc_alu_src         = 0;
    csr_bitmask_sel    = 0;


    case (id_op)
      OPCODE_LOAD : begin
        imm_ext_op = I_ALU_TYPE;
        alu_a_src  = ALU_A_SEL_REG_DATA;
        alu_b_src  = ALU_B_SEL_IMM;
        alu_op     = ALU_OP_ILOAD_S_U_TYPE;
        pc_alu_src = PC_ALU_SEL_PC;
        case (id_funct3)
          FUNCT3_LB : begin
            {is_rd_write, is_rs1_read, is_mem_read, is_memsize_b} = 4'b1111;
          end
          FUNCT3_LH : begin
            {is_rd_write, is_rs1_read, is_mem_read, is_memsize_h} = 4'b1111;
          end
          FUNCT3_LW : begin
            {is_rd_write, is_rs1_read, is_mem_read, is_memsize_w} = 4'b1111;
          end
          FUNCT3_LBU : begin
            {is_rd_write, is_rs1_read, is_mem_read, is_memsize_bu} = 4'b1111;
          end
          FUNCT3_LHU : begin
            {is_rd_write, is_rs1_read, is_mem_read, is_memsize_hu} = 4'b1111;
          end
          default : begin
            illegal_instr_trap = 1;
          end
        endcase
      end

      OPCODE_SYSCALL_CSR : begin
        case (id_funct3)
          FUNCT3_ECALL_EBREAK : begin
            if ((id_rs1_addr == 0) && (id_rd_addr == 0)) begin
              if (id_funct12 == 12'h001) begin
                breakpoint_trap = 1;
              end else if (id_funct12 == 12'h000) begin
                ecall_m_trap = 1;
              end else begin
                illegal_instr_trap = 1;
              end
            end else begin
              illegal_instr_trap = 1;
            end
          end
          // CSRRW/I always writes to the csr file, and conditionally reads when rd is not x0
          FUNCT3_CSRRW : begin
            {is_rs1_read, is_rd_write, is_csr_write, csr_op_rw} = 4'b1111;
            is_csr_read     = (id_rd_addr != 0);
            csr_bitmask_sel = CSR_BITMASK_SEL_REG_DATA;
          end
          FUNCT3_CSRRWI : begin
            {is_rs1_read, is_rd_write, is_csr_write, csr_op_rw} = 4'b1111;
            is_csr_read     = (id_rd_addr != 0);
            imm_ext_op      = CSR_TYPE;
            csr_bitmask_sel = CSR_BITMASK_SEL_IMM;
          end
          // Others always read from the csr file, and conditionally writes when
          // rs1 is x0, or uimm is 0 for register and immediate operand types, respectively
          FUNCT3_CSRRS : begin
            {is_rs1_read, is_rd_write, is_csr_read, csr_op_set} = 4'b1111;
            is_csr_write    = (id_rs1_addr != 0);
            csr_bitmask_sel = CSR_BITMASK_SEL_REG_DATA;
          end
          FUNCT3_CSRRSI : begin
            {is_rs1_read, is_rd_write, is_csr_read, csr_op_set} = 4'b1111;
            is_csr_write    = (id_rs1_addr != 0);
            imm_ext_op      = CSR_TYPE;
            csr_bitmask_sel = CSR_BITMASK_SEL_IMM;
          end
          FUNCT3_CSRRC : begin
            {is_rs1_read, is_rd_write, is_csr_read, csr_op_clear} = 4'b1111;
            is_csr_write    = (id_rs1_addr != 0);
            csr_bitmask_sel = CSR_BITMASK_SEL_REG_DATA;
          end
          FUNCT3_CSRRCI : begin
            {is_rs1_read, is_rd_write, is_csr_read, csr_op_clear} = 4'b1111;
            is_csr_write    = (id_rs1_addr != 0);
            imm_ext_op      = CSR_TYPE;
            csr_bitmask_sel = CSR_BITMASK_SEL_IMM;
          end
          default : begin
            illegal_instr_trap = 1;
          end
        endcase
      end
      OPCODE_STORE : begin
        imm_ext_op = S_TYPE;
        alu_a_src  = ALU_A_SEL_REG_DATA;
        alu_b_src  = ALU_B_SEL_IMM;
        alu_op     = ALU_OP_ILOAD_S_U_TYPE;
        pc_alu_src = PC_ALU_SEL_PC;
        case (id_funct3)
          FUNCT3_SB : begin
            {is_rs1_read, is_rs2_read, is_mem_write, is_memsize_b} = 4'b1111;
          end
          FUNCT3_SH : begin
            {is_rs1_read, is_rs2_read, is_mem_write, is_memsize_h} = 4'b1111;
          end
          FUNCT3_SW : begin
            {is_rs1_read, is_rs2_read, is_mem_write, is_memsize_w} = 4'b1111;
          end
          default : begin
            illegal_instr_trap = 1;
          end
        endcase
      end
      OPCODE_R_TYPE : begin
        if (is_unknown_rtype) begin
          illegal_instr_trap = 1;
        end else begin
          {is_rs1_read, is_rs2_read, is_rd_write} = 3'b111;
          alu_a_src  = ALU_A_SEL_REG_DATA;
          alu_b_src  = ALU_B_SEL_REG_DATA;
          alu_op     = ALU_OP_IALU_ISHIFT_R_TYPE;
          pc_alu_src = PC_ALU_SEL_PC;
        end
      end
      OPCODE_B_TYPE : begin
        {is_rs1_read, is_rs2_read, is_branch} = 3'b111;
        imm_ext_op = B_TYPE;
        alu_a_src  = ALU_A_SEL_REG_DATA;
        alu_b_src  = ALU_B_SEL_REG_DATA;
        alu_op     = ALU_OP_B_TYPE;
        pc_alu_src = PC_ALU_SEL_PC;
      end
      //I-type ALU or shift
      OPCODE_I_TYPE : begin
        if (is_unknown_itype) begin
          illegal_instr_trap = 1;
        end else begin
          alu_a_src  = ALU_A_SEL_REG_DATA;
          alu_b_src  = ALU_B_SEL_IMM;
          alu_op     = ALU_OP_IALU_ISHIFT_R_TYPE;
          pc_alu_src = PC_ALU_SEL_PC;
          case (id_funct3)
            3'b000, 3'b010, 3'b011, 3'b100, 3'b110, 3'b111: begin
              {is_rs1_read, is_rd_write} = 2'b11;
              imm_ext_op = I_ALU_TYPE;  //I-type ALU
            end
            3'b001, 3'b101: begin
              {is_rs1_read, is_rd_write} = 2'b11;
              imm_ext_op = I_SHIFT_TYPE;  //I-type Shift
            end
            default : begin
              illegal_instr_trap = 1;
            end
          endcase  //I-type shift
        end
      end
      OPCODE_JAL : begin
        {is_rd_write, is_jump, is_jal} = 3'b111;
        imm_ext_op = J_TYPE;
        alu_a_src  = ALU_A_SEL_REG_DATA;
        alu_b_src  = ALU_B_SEL_REG_DATA;
        alu_op     = ALU_OP_ILOAD_S_U_TYPE;
        pc_alu_src = PC_ALU_SEL_PC;
      end
      OPCODE_U_TYPE_LUI : begin
        is_rd_write = 1;
        imm_ext_op  = U_TYPE;
        alu_a_src   = ALU_A_SEL_ZERO;
        alu_b_src   = ALU_B_SEL_IMM;
        alu_op      = ALU_OP_ILOAD_S_U_TYPE;
        pc_alu_src  = PC_ALU_SEL_PC;
      end
      OPCODE_U_TYPE_AUIPC : begin
        is_rd_write = 1;
        imm_ext_op  = U_TYPE;
        alu_a_src   = ALU_A_SEL_PC;
        alu_b_src   = ALU_B_SEL_IMM;
        alu_op      = ALU_OP_ILOAD_S_U_TYPE;
        pc_alu_src  = PC_ALU_SEL_PC;
      end
      OPCODE_JALR : begin
        {is_rs1_read, is_rd_write, is_jump, is_jalr} = 4'b1111;
        imm_ext_op = I_ALU_TYPE;
        alu_a_src  = ALU_A_SEL_REG_DATA;
        alu_b_src  = ALU_B_SEL_IMM;
        alu_op     = ALU_OP_ILOAD_S_U_TYPE;
        pc_alu_src = PC_ALU_SEL_REG_DATA;
      end
      default : begin
        illegal_instr_trap = 1;
      end
    endcase
  end



  always @(*) begin
    alu_control = ADD_ALU_CONTROL;
    case (alu_op)
      //I-type Load, S-type, U-type
      ALU_OP_ILOAD_S_U_TYPE :
        alu_control = ADD_ALU_CONTROL;  //add- lw,sw,lb,lh,lbu,lhu,sb,sh,auipc,lui
      //B-type
      ALU_OP_B_TYPE :
        case (id_funct3)
          FUNCT3_BEQ  : alu_control = SUB_ALU_CONTROL;  //sub - beq
          FUNCT3_BNE  : alu_control = NE_ALU_CONTROL;  //sub - bne
          FUNCT3_BLT  : alu_control = LT_ALU_CONTROL;  //blt
          FUNCT3_BGE  : alu_control = GE_ALU_CONTROL;  //bge
          FUNCT3_BLTU : alu_control = LTU_ALU_CONTROL;  //bltu
          FUNCT3_BGEU : alu_control = GEU_ALU_CONTROL;  //bgeu
          default     : ;
        endcase
      //R-type, I-type ALU,I-type 1al shift
      ALU_OP_IALU_ISHIFT_R_TYPE : begin
        case (id_funct3)
          FUNCT3_ADD :
            alu_control = (id_rtype_alt) ? SUB_ALU_CONTROL  /*sub*/ : ADD_ALU_CONTROL  /*add*/;
          FUNCT3_SLL        : alu_control = L_SHIFT_ALU_CONTROL;  //sll
          FUNCT3_SLT        : alu_control = LT_ALU_CONTROL;  //slt
          FUNCT3_SLTU_SLTIU : alu_control = LTU_ALU_CONTROL;  //sltu, sltiu
          FUNCT3_XOR        : alu_control = XOR_ALU_CONTROL;  //xor
          FUNCT3_SRA        :
            alu_control = (id_rtype_alt || id_itype_alt) ? R_SHIFT_A_ALU_CONTROL /*sra*/ : R_SHIFT_L_ALU_CONTROL /*srl*/;
          FUNCT3_OR  : alu_control = OR_ALU_CONTROL;  //or
          FUNCT3_AND : alu_control = AND_ALU_CONTROL;  //and
          default    : ;
        endcase
      end
      default : ;
    endcase
  end

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



  // extend immediate to 32 bit value depending on instruction type
  always @(*) begin
    case (id_imm_ext_op)
      //I-type ALU
      I_ALU_TYPE   : id_imm_ext = {{20{id_q_insn[31]}}, id_q_insn[31:20]};
      //S-type
      S_TYPE       : id_imm_ext = {{20{id_q_insn[31]}}, id_q_insn[31:25], id_q_insn[11:7]};
      //B-type
      B_TYPE       : id_imm_ext = {{20{id_q_insn[31]}}, id_q_insn[7], id_q_insn[30:25], id_q_insn[11:8], 1'b0};
      //J-type
      J_TYPE       : id_imm_ext = {{12{id_q_insn[31]}}, id_q_insn[19:12], id_q_insn[20], id_q_insn[30:21], 1'b0};
      //I-type Shift
      I_SHIFT_TYPE : id_imm_ext = {27'd0, id_q_insn[24:20]};
      //U-type lui
      U_TYPE       : id_imm_ext = {id_q_insn[31:12], 12'd0};
      // immediate type CSR instruction
      CSR_TYPE     : id_imm_ext = {27'd0, id_q_insn[19:15]};
      default      : id_imm_ext = 0;
    endcase
  end

  // compute branch address early to reduce combinational path of branch prediction
  assign id_branch_addr = id_q_pc +
    {{20{id_q_insn[31]}}, id_q_insn[7], id_q_insn[30:25], id_q_insn[11:8], 1'b0};
  // assign signals propagating to the next stage
  always @(*)
  begin
    id_op               = id_q_insn[6:0];
    id_funct3           = id_q_insn[14:12];
    id_funct7b5         = id_q_insn[30];
    id_funct7           = id_q_insn[31:25];
    id_funct12          = id_q_insn[31:20];
    id_rtype_alt        = id_op[5] & id_funct7b5;
    id_itype_alt        = ~id_op[5] & id_funct7b5;
    id_rs1_addr         = id_is_rs1_read ? id_q_insn[19:15] : 0;
    id_rs2_addr         = id_is_rs2_read ? id_q_insn[24:20] : 0;
    id_rd_addr          = id_q_insn[11:7];
    id_csr_addr         = id_q_insn[31:20];
    // Branch and jump
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



  //*****************************************************************
  //
  //
  // INSTRUCTION EXECUTE STAGE
  //
  //
  //*****************************************************************

  // select rs1 read data
  always @(*) begin
    case (ex_forward_rs1_sel)
      NO_FORWARD_SEL :
        ex_rs1_rdata = ex_q_rs1_rdata;
      FORWARD_SEL_MEM_RESULT :
        ex_rs1_rdata = mem_q_alu_csr_result;
      FORWARD_SEL_WB_RESULT :
        ex_rs1_rdata = wb_rd_wdata;
      default :
        ex_rs1_rdata = 0;
    endcase
  end

// select input data for the first alu input
  always @(*) begin
    case (ex_q_alu_a_sel)
      ALU_A_SEL_REG_DATA :
        ex_src_a = ex_rs1_rdata;
      ALU_A_SEL_PC :
        ex_src_a = ex_q_pc;
      ALU_A_SEL_ZERO :
        ex_src_a = 0;
      default :
        ex_src_a = 0;
    endcase
  end

// select rs2 read data
  always @(*) begin
    case (ex_forward_rs2_sel)
      NO_FORWARD_SEL :
        ex_rs2_rdata = ex_q_rs2_rdata;
      FORWARD_SEL_MEM_RESULT :
        ex_rs2_rdata = mem_q_alu_csr_result;
      FORWARD_SEL_WB_RESULT :
        ex_rs2_rdata = wb_rd_wdata;
      default :
        ex_rs2_rdata = 0;
    endcase
  end

// select input data for the second alu input
  always @(*) begin
    case (ex_q_alu_b_sel)
      ALU_B_SEL_REG_DATA :
        ex_src_b = ex_rs2_rdata;
      ALU_B_SEL_IMM :
        ex_src_b = ex_q_imm_ext;
      default :
        ex_src_b = 0;
    endcase
  end

// select base value for pc offset
  always @(*) begin
    case (ex_q_pc_alu_sel)
      PC_ALU_SEL_REG_DATA :
        ex_pc_base = ex_rs1_rdata;
      PC_ALU_SEL_PC :
        ex_pc_base = ex_q_pc;
      default :
        ex_pc_base = 0;
    endcase
  end

// select bitmask source for csr op
  always @(*) begin
    case (ex_q_csr_bitmask_sel)
      CSR_BITMASK_SEL_REG_DATA :
        ex_csr_bitmask = ex_rs1_rdata;
      CSR_BITMASK_SEL_IMM :
        ex_csr_bitmask = ex_q_imm_ext;
      default :
        ex_csr_bitmask = 0;
    endcase
  end

// select csr result depending on op type
  always @(*) begin
    if (ex_q_csr_op_rw) begin
      ex_csr_wdata = ex_csr_bitmask;
    end
    else if (ex_q_csr_op_clear) begin
      ex_csr_wdata = (ex_q_csr_rdata & ~ex_csr_bitmask);
    end
    else if (ex_q_csr_op_set) begin
      ex_csr_wdata = (ex_q_csr_rdata | ex_csr_bitmask);
    end
    else begin
      ex_csr_wdata = 0;
    end
  end
  // trap if the jump address is not word aligned
  // jump if instruction is a jump or a branch and condition is true
  // jump is delayed to the mem stage to avoid long combinational path
  assign ex_jaddr           = (ex_q_is_jalr) ? ((ex_pc_base + ex_q_imm_ext) & ~(1'b1)) : (ex_pc_base + ex_q_imm_ext);
  assign ex_jump_taken      = (ex_q_is_jump | (ex_q_is_branch & ex_branch_cond));
  assign ex_misaligned_jump = ex_jump_taken & (ex_jaddr[1] | ex_jaddr[0]);

  always @(*)
    begin
      // Branch and jump
      ex_d_is_branch      = ex_q_is_branch;
      ex_d_is_jump        = ex_q_is_jump;
      ex_d_is_jal         = ex_q_is_jal;
      ex_d_is_jalr        = ex_q_is_jalr;
      ex_d_branch_predict = ex_q_branch_predict;
      ex_d_pht_idx        = ex_q_pht_idx;

      // CSR operations
      ex_d_is_csr_write = ex_q_is_csr_write;
      ex_d_is_csr_read  = ex_q_is_csr_read;

      // Register writes
      if (ex_misaligned_jump)
        ex_d_is_rd_write = 0;
      else
        ex_d_is_rd_write = ex_q_is_rd_write;

      // Memory access
      ex_d_is_mem_write = ex_q_is_mem_write;
      ex_d_is_mem_read  = ex_q_is_mem_read;

      // Memory size indicators
      ex_d_is_memsize_b  = ex_q_is_memsize_b;
      ex_d_is_memsize_bu = ex_q_is_memsize_bu;
      ex_d_is_memsize_h  = ex_q_is_memsize_h;
      ex_d_is_memsize_hu = ex_q_is_memsize_hu;
      ex_d_is_memsize_w  = ex_q_is_memsize_w;

      // pipeline
      ex_d_valid          = ex_q_valid;
      ex_d_pc             = ex_q_pc;
      ex_d_pc_plus_4      = ex_q_pc_plus_4;
      ex_d_rd_addr        = ex_q_rd_addr;
      ex_d_csr_addr       = ex_q_csr_addr;
      ex_d_csr_wdata      = ex_csr_wdata;
      ex_d_store_wdata    = ex_rs2_rdata;
      ex_d_alu_csr_result = (ex_q_is_csr_read) ? ex_q_csr_rdata : ex_alu_result;
      ex_d_jaddr          = ex_jaddr;
      ex_d_jump_taken     = ex_jump_taken;
      // traps
      if (ex_q_trap_valid)
        begin
          ex_d_trap_valid  = 1;
          ex_d_trap_mcause = ex_q_trap_mcause;
          ex_d_trap_pc     = ex_q_trap_pc;
        end
      else if (ex_misaligned_jump)
        begin
          ex_d_trap_valid  = 1;
          ex_d_trap_mcause = {1'b0, TRAP_CODE_INSTR_ADDR_MISALIGNED};
          ex_d_trap_pc     = ex_q_pc;
        end
      else
        begin
          ex_d_trap_valid  = 0;
          ex_d_trap_mcause = 0;
          ex_d_trap_pc     = 0;
        end
    end

  // calculates the branch condition of the instruction
  always @(*) begin
    case (ex_q_alu_control)
      SUB_ALU_CONTROL : ex_branch_cond = (ex_src_a == ex_src_b);  // beq
      NE_ALU_CONTROL  : ex_branch_cond = (ex_src_a != ex_src_b);
      LT_ALU_CONTROL  : ex_branch_cond = ($signed(ex_src_a) < $signed(ex_src_b));
      LTU_ALU_CONTROL : ex_branch_cond = (ex_src_a < ex_src_b);
      GE_ALU_CONTROL  : ex_branch_cond = ($signed(ex_src_a) >= $signed(ex_src_b));
      GEU_ALU_CONTROL : ex_branch_cond = (ex_src_a >= ex_src_b);
      default         : ex_branch_cond = 0;
    endcase
  end

  // calculates the result of the instruction
  always @(*) begin
    case (ex_q_alu_control)
      ADD_ALU_CONTROL       : ex_alu_result = ex_src_a + ex_src_b;
      SUB_ALU_CONTROL       : ex_alu_result = ex_src_a - ex_src_b;
      AND_ALU_CONTROL       : ex_alu_result = ex_src_a & ex_src_b;
      OR_ALU_CONTROL        : ex_alu_result = ex_src_a | ex_src_b;
      XOR_ALU_CONTROL       : ex_alu_result = ex_src_a ^ ex_src_b;
      LT_ALU_CONTROL, LTU_ALU_CONTROL: ex_alu_result = {31'd0, ex_branch_cond};
      L_SHIFT_ALU_CONTROL   : ex_alu_result = ex_src_a << ex_src_b[4:0];
      R_SHIFT_L_ALU_CONTROL : ex_alu_result = ex_src_a >> ex_src_b[4:0];
      R_SHIFT_A_ALU_CONTROL : ex_alu_result = $signed(ex_src_a) >>> ex_src_b[4:0];
      default               : ex_alu_result = 0;
    endcase
  end

`ifdef RISCV_FORMAL

  wire [31:0] ex_next_pc;
  assign ex_next_pc = (ex_jump_taken) ? ex_jaddr : ex_q_pc_plus_4;
  always @(*)
  begin
    // additional stage info
    ex_d_next_pc   = ex_next_pc;
    ex_d_insn      = ex_q_insn;
    ex_d_intr      = ex_q_intr;
    ex_d_rs1_addr  = ex_q_rs1_addr;
    ex_d_rs2_addr  = ex_q_rs2_addr;
    ex_d_rs1_rdata = ex_rs1_rdata;
    ex_d_rs2_rdata = ex_rs2_rdata;
    ex_d_csr_rdata = ex_q_csr_rdata;
    if (ex_q_trap_valid) // if trap from previous stage save it instead
      begin
        ex_d_trap_insn      = ex_q_trap_insn;
        ex_d_trap_next_pc   = ex_q_trap_next_pc;
        ex_d_trap_rs1_addr  = ex_q_trap_rs1_addr;
        ex_d_trap_rs2_addr  = ex_q_trap_rs2_addr;
        ex_d_trap_rd_addr   = ex_q_trap_rd_addr;
        ex_d_trap_rs1_rdata = ex_q_trap_rs1_rdata;
        ex_d_trap_rs2_rdata = ex_q_trap_rs2_rdata;
        ex_d_trap_rd_wdata  = ex_q_trap_rd_wdata;
      end else begin
      ex_d_trap_insn      = ex_q_insn;
      ex_d_trap_next_pc   = ex_next_pc;
      ex_d_trap_rs1_addr  = ex_q_rs1_addr;
      ex_d_trap_rs2_addr  = ex_q_rs2_addr;
      ex_d_trap_rd_addr   = ex_q_rd_addr;
      ex_d_trap_rs1_rdata = ex_src_a;
      ex_d_trap_rs2_rdata = ex_rs2_rdata;
      ex_d_trap_rd_wdata  = 0;
    end

  end
`endif
  //*****************************************************************
  //
  //
  // DATA MEMORY STAGE
  //
  //
  //*****************************************************************
  wire [4:0] load_size_onehot ;
  wire [2:0] store_size_onehot;
  wire mem_valid;
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
    .pulse_o(mem_valid                   )
  );
  assign mem_valid_o = mem_valid;
  //*****************************************************************
  //
  //
  // LOAD UNIT
  //
  //
  //*****************************************************************

  wire [31:0] loaded;
  assign loaded = mem_rdata_i >> 8 * (mem_q_alu_csr_result[1:0]);
  // logic to determine which bits of the read data from data memory will be loaded for load instructions
  always @(*) begin
    misaligned_load = 0;
    mem_rstrb       = 0;
    mem_load_rdata  = 0;
    if (load_size_onehot[0]) begin  // byte
      // never misaligned
      mem_rstrb      = 4'h1 << mem_q_alu_csr_result[1:0];
      mem_load_rdata = {{24{loaded[7]}}, loaded[7:0]};
    end else if (load_size_onehot[1]) begin  // byte unsigned
      // never misaligned
      mem_rstrb      = 4'h1 << mem_q_alu_csr_result[1:0];
      mem_load_rdata = {{24{1'b0}}, loaded[7:0]};
    end else if (load_size_onehot[2]) begin  // half
      // misaligned when lsb = 1
      misaligned_load = mem_q_alu_csr_result[0];
      mem_rstrb       = 4'h3 << (mem_q_alu_csr_result[1] * 2);
      mem_load_rdata  = {{16{loaded[15]}}, loaded[15:0]};
    end else if (load_size_onehot[3]) begin  // half unsigned
      // misaligned when lsb = 1
      misaligned_load = mem_q_alu_csr_result[0];
      mem_rstrb       = 4'h3 << (mem_q_alu_csr_result[1] * 2);
      mem_load_rdata  = {{16{1'b0}}, loaded[15:0]};
    end else if (load_size_onehot[4]) begin  // word
      // misaligned when at least one of the lower 2 bits are nonzero
      misaligned_load = |mem_q_alu_csr_result[1:0];
      mem_rstrb       = 4'hf;
      mem_load_rdata  = loaded;
    end else begin
      mem_rstrb       = 0;
      misaligned_load = 0;
    end
  end

  //*****************************************************************
  //
  //
  // STORE UNIT
  //
  //
  //*****************************************************************
  always @(*) begin
    misaligned_store = 0;
    mem_wdata_o      = 0;
    mem_wstrb        = 0;
    if (store_size_onehot[0]) begin // byte
      // never misaligned
      mem_wstrb   = 4'b1 << mem_q_alu_csr_result[1:0];
      mem_wdata_o = mem_q_store_wdata << mem_q_alu_csr_result[1:0] * 8;
    end else if (store_size_onehot[1]) begin // half
      // misaligned when lsb = 1
      misaligned_store = mem_q_alu_csr_result[0];
      mem_wstrb        = 4'h3 << mem_q_alu_csr_result[1] * 2;
      mem_wdata_o      = mem_q_store_wdata << mem_q_alu_csr_result[1] * 16;
    end else if (store_size_onehot[2]) begin // word
      // misaligned when lsbs[1:0] != 2'b00
      misaligned_store = |mem_q_alu_csr_result[1:0];
      mem_wstrb        = 4'hf;
      mem_wdata_o      = mem_q_store_wdata;
    end else begin
      mem_wstrb        = 0;
      misaligned_store = 0;
    end
  end

  always @(*)
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
  always @(*)
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

  //*****************************************************************
  //
  //
  // WRITEBACK STAGE
  //
  //
  //*****************************************************************


  always @(*)
    begin
      wb_trap_mcause = wb_q_trap_mcause;
      wb_trap_pc     = wb_q_trap_pc;
      wb_rd_addr     = wb_q_rd_addr;
      wb_rd_wdata    = wb_q_rd_wdata;
      wb_csr_addr    = wb_q_csr_addr;
      wb_csr_wdata   = wb_q_csr_wdata;
    end

  //*****************************************************************
  //
  //
  // PIPELINE REGISTERS
  //
  //
  //*****************************************************************


//-------------------------------
// IF/ID pipeline
//-------------------------------
  always @(posedge clk_i) begin
    // clear the pipeline on reset, flush,
    // or imem buffer invalid AND the
    // stage is not stalled
    if (rst_i || if_id_flush || (!if_id_stall && !imem_rdata_valid)) begin
      // clear all IF/ID pipeline registers
      id_q_valid     <= 0;
      id_q_pc        <= 0;
      id_q_pc_plus_4 <= 0;
      id_q_insn      <= NOP_INSTRUCTION;
`ifdef RISCV_FORMAL
      id_q_intr <= 0;
`endif
    end else if (!if_id_stall) begin
      // propagate IF stage outputs to ID stage
      id_q_valid     <= if_d_valid;
      id_q_pc        <= if_d_pc;
      id_q_pc_plus_4 <= if_d_pc_plus_4;
      id_q_insn      <= if_d_insn;
`ifdef RISCV_FORMAL
      id_q_intr <= if_d_intr;
`endif
    end
  end


//-------------------------------
// ID/EX pipeline
//-------------------------------
  always @(posedge clk_i) begin
    // clear the pipeline on reset, flush,
    // or imem buffer invalid AND the stage is not stalled
    if (rst_i || id_ex_flush || (!id_ex_stall && if_id_stall)) begin
      // clear all EX stage registers
      ex_q_valid     <= 0;
      ex_q_pc        <= 0;
      ex_q_pc_plus_4 <= 0;
      ex_q_rs1_addr  <= 0;
      ex_q_rs2_addr  <= 0;
      ex_q_rd_addr   <= 0;
      ex_q_rs1_rdata <= 0;
      ex_q_rs2_rdata <= 0;
      ex_q_imm_ext   <= 0;
      ex_q_csr_addr  <= 0;
      ex_q_csr_rdata <= 0;

      ex_q_alu_control     <= 0;
      ex_q_alu_a_sel       <= 0;
      ex_q_alu_b_sel       <= 0;
      ex_q_pc_alu_sel      <= 0;
      ex_q_csr_bitmask_sel <= 0;

      ex_q_is_branch    <= 0;
      ex_q_is_jump      <= 0;
      ex_q_is_csr_write <= 0;
      ex_q_is_csr_read  <= 0;
      ex_q_is_rd_write  <= 0;
      ex_q_is_rs1_read  <= 0;
      ex_q_is_rs2_read  <= 0;
      ex_q_is_mem_write <= 0;
      ex_q_is_mem_read  <= 0;

      ex_q_is_jal        <= 0;
      ex_q_is_jalr       <= 0;
      ex_q_is_memsize_b  <= 0;
      ex_q_is_memsize_bu <= 0;
      ex_q_is_memsize_h  <= 0;
      ex_q_is_memsize_hu <= 0;
      ex_q_is_memsize_w  <= 0;

      ex_q_csr_op_rw    <= 0;
      ex_q_csr_op_clear <= 0;
      ex_q_csr_op_set   <= 0;

      ex_q_branch_predict <= 0;
      ex_q_pht_idx        <= 0;

      ex_q_trap_valid  <= 0;
      ex_q_trap_mcause <= 0;
      ex_q_trap_pc     <= 0;

`ifdef RISCV_FORMAL
      ex_q_insn <= 0;
      ex_q_intr <= 0;

      ex_q_trap_insn      <= 0;
      ex_q_trap_next_pc   <= 0;
      ex_q_trap_rs1_addr  <= 0;
      ex_q_trap_rs2_addr  <= 0;
      ex_q_trap_rd_addr   <= 0;
      ex_q_trap_rs1_rdata <= 0;
      ex_q_trap_rs2_rdata <= 0;
      ex_q_trap_rd_wdata  <= 0;
`endif

    end else if (!if_id_stall) begin
      // propagate ID stage values to EX stage
      ex_q_valid     <= id_d_valid;
      ex_q_pc        <= id_d_pc;
      ex_q_pc_plus_4 <= id_d_pc_plus_4;
      ex_q_rs1_addr  <= id_d_rs1_addr;
      ex_q_rs2_addr  <= id_d_rs2_addr;
      ex_q_rd_addr   <= id_d_rd_addr;
      ex_q_rs1_rdata <= id_d_rs1_rdata;
      ex_q_rs2_rdata <= id_d_rs2_rdata;
      ex_q_imm_ext   <= id_d_imm_ext;
      ex_q_csr_addr  <= id_d_csr_addr;
      ex_q_csr_rdata <= id_d_csr_rdata;

      ex_q_alu_control     <= id_d_alu_control;
      ex_q_alu_a_sel       <= id_d_alu_a_sel;
      ex_q_alu_b_sel       <= id_d_alu_b_sel;
      ex_q_pc_alu_sel      <= id_d_pc_alu_sel;
      ex_q_csr_bitmask_sel <= id_d_csr_bitmask_sel;

      ex_q_is_branch    <= id_d_is_branch;
      ex_q_is_jump      <= id_d_is_jump;
      ex_q_is_csr_write <= id_d_is_csr_write;
      ex_q_is_csr_read  <= id_d_is_csr_read;
      ex_q_is_rd_write  <= id_d_is_rd_write;
      ex_q_is_rs1_read  <= id_d_is_rs1_read;
      ex_q_is_rs2_read  <= id_d_is_rs2_read;
      ex_q_is_mem_write <= id_d_is_mem_write;
      ex_q_is_mem_read  <= id_d_is_mem_read;

      ex_q_is_jal        <= id_d_is_jal;
      ex_q_is_jalr       <= id_d_is_jalr;
      ex_q_is_memsize_b  <= id_d_is_memsize_b;
      ex_q_is_memsize_bu <= id_d_is_memsize_bu;
      ex_q_is_memsize_h  <= id_d_is_memsize_h;
      ex_q_is_memsize_hu <= id_d_is_memsize_hu;
      ex_q_is_memsize_w  <= id_d_is_memsize_w;

      ex_q_csr_op_rw    <= id_d_csr_op_rw;
      ex_q_csr_op_clear <= id_d_csr_op_clear;
      ex_q_csr_op_set   <= id_d_csr_op_set;

      ex_q_branch_predict <= id_d_branch_predict;
      ex_q_pht_idx        <= id_d_pht_idx;

      ex_q_trap_valid  <= id_d_trap_valid;
      ex_q_trap_mcause <= id_d_trap_mcause;
      ex_q_trap_pc     <= id_d_trap_pc;

`ifdef RISCV_FORMAL
      ex_q_insn <= id_d_insn;
      ex_q_intr <= id_d_intr;

      ex_q_trap_insn      <= id_d_trap_insn;
      ex_q_trap_next_pc   <= id_d_trap_next_pc;
      ex_q_trap_rs1_addr  <= id_d_trap_rs1_addr;
      ex_q_trap_rs2_addr  <= id_d_trap_rs2_addr;
      ex_q_trap_rd_addr   <= id_d_trap_rd_addr;
      ex_q_trap_rs1_rdata <= id_d_trap_rs1_rdata;
      ex_q_trap_rs2_rdata <= id_d_trap_rs2_rdata;
      ex_q_trap_rd_wdata  <= id_d_trap_rd_wdata;
`endif
    end
  end



//-------------------------------
// EX/MEM pipeline
//-------------------------------
always @(posedge clk_i) begin
    if (rst_i || ex_mem_flush || (!ex_mem_stall && id_ex_stall)) begin
        // clear EX/MEM pipeline registers
        mem_q_valid        <= 0;
        mem_q_pc           <= 0;
        mem_q_pc_plus_4    <= 0;
        mem_q_rd_addr      <= 0;
        mem_q_csr_addr     <= 0;
        mem_q_csr_wdata    <= 0;
        mem_q_store_wdata  <= 0;
        mem_q_alu_csr_result <= 0;

        mem_q_is_branch    <= 0;
        mem_q_is_jump      <= 0;
        mem_q_is_csr_write <= 0;
        mem_q_is_csr_read  <= 0;
        mem_q_is_rd_write  <= 0;
        mem_q_is_mem_write <= 0;
        mem_q_is_mem_read  <= 0;

        mem_q_is_jal       <= 0;
        mem_q_is_jalr      <= 0;
        mem_q_is_memsize_b <= 0;
        mem_q_is_memsize_bu<= 0;
        mem_q_is_memsize_h <= 0;
        mem_q_is_memsize_hu<= 0;
        mem_q_is_memsize_w <= 0;

        mem_q_branch_predict <= 0;
        mem_q_pht_idx        <= 0;

        mem_q_jump_taken   <= 0;
        mem_q_jaddr        <= 0;

        mem_q_trap_valid   <= 0;
        mem_q_trap_mcause  <= 0;
        mem_q_trap_pc      <= 0;

`ifdef RISCV_FORMAL
        mem_q_insn        <= 0;
        mem_q_intr        <= 0;
        mem_q_next_pc     <= 0;
        mem_q_csr_rdata   <= 0;
        mem_q_rs1_addr    <= 0;
        mem_q_rs2_addr    <= 0;
        mem_q_rs1_rdata   <= 0;
        mem_q_rs2_rdata   <= 0;
        mem_q_trap_insn       <= 0;
        mem_q_trap_next_pc    <= 0;
        mem_q_trap_rs1_addr   <= 0;
        mem_q_trap_rs2_addr   <= 0;
        mem_q_trap_rd_addr    <= 0;
        mem_q_trap_rs1_rdata  <= 0;
        mem_q_trap_rs2_rdata  <= 0;
        mem_q_trap_rd_wdata   <= 0;
`endif
    end else if (!ex_mem_stall) begin
        // propagate EX stage outputs to MEM stage
        mem_q_valid        <= ex_d_valid;
        mem_q_pc           <= ex_d_pc;
        mem_q_pc_plus_4    <= ex_d_pc_plus_4;
        mem_q_rd_addr      <= ex_d_rd_addr;
        mem_q_csr_addr     <= ex_d_csr_addr;
        mem_q_csr_wdata    <= ex_d_csr_wdata;
        mem_q_store_wdata  <= ex_d_store_wdata;
        mem_q_alu_csr_result <= ex_d_alu_csr_result;

        mem_q_is_branch    <= ex_d_is_branch;
        mem_q_is_jump      <= ex_d_is_jump;
        mem_q_is_csr_write <= ex_d_is_csr_write;
        mem_q_is_csr_read  <= ex_d_is_csr_read;
        mem_q_is_rd_write  <= ex_d_is_rd_write;
        mem_q_is_mem_write <= ex_d_is_mem_write;
        mem_q_is_mem_read  <= ex_d_is_mem_read;

        mem_q_is_jal       <= ex_d_is_jal;
        mem_q_is_jalr      <= ex_d_is_jalr;
        mem_q_is_memsize_b <= ex_d_is_memsize_b;
        mem_q_is_memsize_bu<= ex_d_is_memsize_bu;
        mem_q_is_memsize_h <= ex_d_is_memsize_h;
        mem_q_is_memsize_hu<= ex_d_is_memsize_hu;
        mem_q_is_memsize_w <= ex_d_is_memsize_w;

        mem_q_branch_predict <= ex_d_branch_predict;
        mem_q_pht_idx        <= ex_d_pht_idx;

        mem_q_jump_taken   <= ex_d_jump_taken;
        mem_q_jaddr        <= ex_d_jaddr;

        mem_q_trap_valid   <= ex_d_trap_valid;
        mem_q_trap_mcause  <= ex_d_trap_mcause;
        mem_q_trap_pc      <= ex_d_trap_pc;

`ifdef RISCV_FORMAL
        mem_q_insn        <= ex_d_insn;
        mem_q_intr        <= ex_d_intr;
        mem_q_next_pc     <= ex_d_next_pc;
        mem_q_csr_rdata   <= ex_d_csr_rdata;
        mem_q_rs1_addr    <= ex_d_rs1_addr;
        mem_q_rs2_addr    <= ex_d_rs2_addr;
        mem_q_rs1_rdata   <= ex_d_rs1_rdata;
        mem_q_rs2_rdata   <= ex_d_rs2_rdata;
        mem_q_trap_insn       <= ex_d_trap_insn;
        mem_q_trap_next_pc    <= ex_d_trap_next_pc;
        mem_q_trap_rs1_addr   <= ex_d_trap_rs1_addr;
        mem_q_trap_rs2_addr   <= ex_d_trap_rs2_addr;
        mem_q_trap_rd_addr    <= ex_d_trap_rd_addr;
        mem_q_trap_rs1_rdata  <= ex_d_trap_rs1_rdata;
        mem_q_trap_rs2_rdata  <= ex_d_trap_rs2_rdata;
        mem_q_trap_rd_wdata   <= ex_d_trap_rd_wdata;
`endif
    end
end

//-------------------------------
// MEM/WB pipeline
//-------------------------------
always @(posedge clk_i) begin
    if (rst_i || mem_wb_flush || (!mem_wb_stall && ex_mem_stall)) begin
        // clear MEM/WB pipeline registers
        wb_q_valid       <= 0;
        wb_q_rd_addr     <= 0;
        wb_q_csr_addr    <= 0;
        wb_q_csr_wdata   <= 0;
        wb_q_rd_wdata    <= 0;
        wb_q_pc_plus_4   <= 0;

        wb_q_is_csr_write <= 0;
        wb_q_is_csr_read  <= 0;
        wb_q_is_rd_write  <= 0;

        wb_q_trap_valid   <= 0;
        wb_q_trap_mcause  <= 0;
        wb_q_trap_pc      <= 0;

`ifdef RISCV_FORMAL
        wb_q_pc           <= 0;
        wb_q_next_pc      <= 0;
        wb_q_insn         <= 0;
        wb_q_intr         <= 0;
        wb_q_csr_rdata    <= 0;
        wb_q_mem_addr     <= 0;
        wb_q_load_rdata   <= 0;
        wb_q_rs1_addr     <= 0;
        wb_q_rs2_addr     <= 0;
        wb_q_rs1_rdata    <= 0;
        wb_q_rs2_rdata    <= 0;
        wb_q_load_rmask   <= 0;
        wb_q_store_wmask  <= 0;
        wb_q_store_wdata  <= 0;
        wb_q_trap_insn       <= 0;
        wb_q_trap_next_pc    <= 0;
        wb_q_trap_rs1_addr   <= 0;
        wb_q_trap_rs2_addr   <= 0;
        wb_q_trap_rd_addr    <= 0;
        wb_q_trap_rs1_rdata  <= 0;
        wb_q_trap_rs2_rdata  <= 0;
        wb_q_trap_rd_wdata   <= 0;
`endif
    end else if (!mem_wb_stall) begin
        // propagate MEM stage outputs to WB stage
        wb_q_valid       <= mem_d_valid;
        wb_q_rd_addr     <= mem_d_rd_addr;
        wb_q_csr_addr    <= mem_d_csr_addr;
        wb_q_csr_wdata   <= mem_d_csr_wdata;
        wb_q_rd_wdata    <= mem_d_rd_wdata;
        wb_q_pc_plus_4   <= mem_d_pc_plus_4;

        wb_q_is_csr_write <= mem_d_is_csr_write;
        wb_q_is_csr_read  <= mem_d_is_csr_read;
        wb_q_is_rd_write  <= mem_d_is_rd_write;

        wb_q_trap_valid   <= mem_d_trap_valid;
        wb_q_trap_mcause  <= mem_d_trap_mcause;
        wb_q_trap_pc      <= mem_d_trap_pc;

`ifdef RISCV_FORMAL
        wb_q_pc           <= mem_d_pc;
        wb_q_next_pc      <= mem_d_next_pc;
        wb_q_insn         <= mem_d_insn;
        wb_q_intr         <= mem_d_intr;
        wb_q_csr_rdata    <= mem_d_csr_rdata;
        wb_q_mem_addr     <= mem_d_mem_addr;
        wb_q_load_rdata   <= mem_d_load_rdata;
        wb_q_rs1_addr     <= mem_d_rs1_addr;
        wb_q_rs2_addr     <= mem_d_rs2_addr;
        wb_q_rs1_rdata    <= mem_d_rs1_rdata;
        wb_q_rs2_rdata    <= mem_d_rs2_rdata;
        wb_q_load_rmask   <= mem_d_load_rmask;
        wb_q_store_wmask  <= mem_d_store_wmask;
        wb_q_store_wdata  <= mem_d_store_wdata;
        wb_q_trap_insn       <= mem_d_trap_insn;
        wb_q_trap_next_pc    <= mem_d_trap_next_pc;
        wb_q_trap_rs1_addr   <= mem_d_trap_rs1_addr;
        wb_q_trap_rs2_addr   <= mem_d_trap_rs2_addr;
        wb_q_trap_rd_addr    <= mem_d_trap_rd_addr;
        wb_q_trap_rs1_rdata  <= mem_d_trap_rs1_rdata;
        wb_q_trap_rs2_rdata  <= mem_d_trap_rs2_rdata;
        wb_q_trap_rd_wdata   <= mem_d_trap_rd_wdata;
`endif
    end
end



  //*****************************************************************
  //
  //
  // REGISTER FILE
  //
  //
  //*****************************************************************

  integer        regfile_idx      ;
  reg     [31:0] regfile_arr[0:31];
  // three ported register file
  // read two ports combinationally (A1/RD1, A2/RD2)
  // write third port on rising edge of clock (A3/WD3/WE3)
  // register 0 hardwired to 0
  always @(posedge clk_i) begin
    if (rst_i) begin
      for (regfile_idx = 0; regfile_idx < 32; regfile_idx = regfile_idx + 1) regfile_arr[regfile_idx] <= 32'd0;
    end else if (wb_q_is_rd_write) begin
      if (wb_rd_addr != 0) regfile_arr[wb_rd_addr] <= wb_rd_wdata;
    end
  end
  assign regfile_rs1_rdata = regfile_arr[id_rs1_addr];
  assign regfile_rs2_rdata = regfile_arr[id_rs2_addr];

  //*****************************************************************
  //
  //
  // CSR FILE
  //
  //
  //*****************************************************************

  reg [31:0] csr_mtvec_reg    ;
  reg [31:0] csr_mscratch_reg ;
  reg [31:0] csr_mepc_reg     ;
  reg [31:0] csr_mcause_reg   ;
  reg [31:0] csr_mtval_reg    ;
  reg [63:0] csr_mcycle_reg   ;
  reg [63:0] csr_minstret_reg ;
  reg [31:0] csr_mtvec_next   ;
  reg [31:0] csr_mscratch_next;
  reg [31:0] csr_mepc_next    ;
  reg [31:0] csr_mcause_next  ;
  reg [31:0] csr_mtval_next   ;
  reg [63:0] csr_mcycle_next  ;
  reg [63:0] csr_minstret_next;

  // asserted when writing to a read only register
  // rmask  bits are set if rd != 0 and addr = valid_csr_addr
  // wmask bits are set if csr_wtype != 0

  // read from the csr register file in the ID stage
  always @(*) begin
    csrfile_rdata = 0;
    case (id_csr_addr)
      CSR_ADDR_MTVEC    : csrfile_rdata = csr_mtvec_reg;
      CSR_ADDR_MSCRATCH : csrfile_rdata = csr_mscratch_reg;
      CSR_ADDR_MEPC     : csrfile_rdata = csr_mepc_reg;
      CSR_ADDR_MCAUSE   : csrfile_rdata = csr_mcause_reg;
      CSR_ADDR_MTVAL    : csrfile_rdata = csr_mtval_reg;
      CSR_ADDR_MCYCLE   : csrfile_rdata = csr_mcycle_reg[31:0];
      CSR_ADDR_MCYCLEH  : csrfile_rdata = csr_mcycle_reg[63:32];
      // since we are reading in ID stage add stages that will retire before to the count
      CSR_ADDR_MINSTRET : csrfile_rdata = csr_minstret_reg[31:0] + ex_q_valid
        + mem_q_valid + wb_q_valid;
      CSR_ADDR_MINSTRETH : csrfile_rdata = csr_minstret_reg[63:32];
      default            : ;
    endcase
  end

  // write to the csr register file in the WB stage
  // first, get the next value for each csr
  always @(*) begin
    csr_mtvec_next    = csr_mtvec_reg;
    csr_mscratch_next = csr_mscratch_reg;
    csr_mepc_next     = (wb_q_valid && wb_q_trap_valid) ? wb_trap_pc : csr_mepc_reg;
    csr_mcause_next   = (wb_q_valid && wb_q_trap_valid) ? wb_trap_mcause : csr_mcause_reg;
    csr_mtval_next    = csr_mtval_reg;
    csr_mcycle_next   = csr_mcycle_reg + 1;
    csr_minstret_next = wb_q_valid ? csr_minstret_reg + 1 : csr_minstret_reg;
    case (wb_csr_addr)
      CSR_ADDR_MTVEC    : csr_mtvec_next = wb_csr_wdata & 32'hffff_fffc;
      CSR_ADDR_MSCRATCH : csr_mscratch_next = wb_csr_wdata;
      CSR_ADDR_MEPC     : csr_mepc_next = wb_csr_wdata;
      CSR_ADDR_MCAUSE   : csr_mcause_next = wb_csr_wdata;
      CSR_ADDR_MTVAL    : csr_mtval_next = wb_csr_wdata;
      /*
      READ ONLY CSRS:
      CSR_ADDR_MCYCLE
      CSR_ADDR_MCYCLEH
      CSR_ADDR_MINSTRET
      CSR_ADDR_MINSTRETH
      */
      default           : ;
    endcase
  end

  // write the next csr value to each csr
  always @(posedge clk_i) begin
    if (rst_i) begin
      csr_mtvec_reg    <= 0;
      csr_mscratch_reg <= 0;
      csr_mepc_reg     <= 0;
      csr_mcause_reg   <= 0;
      csr_mtval_reg    <= 0;
      csr_mcycle_reg   <= 0;
      csr_minstret_reg <= 0;
    end else begin
      // use a write enable for csr registers that can be written to
      if (wb_q_is_csr_write) begin
        csr_mtvec_reg    <= csr_mtvec_next;
        csr_mscratch_reg <= csr_mscratch_next;
        csr_mepc_reg     <= csr_mepc_next;
        csr_mcause_reg   <= csr_mcause_next;
        csr_mtval_reg    <= csr_mtval_next;
      end
      csr_mcycle_reg   <= csr_mcycle_next;
      csr_minstret_reg <= csr_minstret_next;
    end
  end

  // synchronously update the trap handler register
  always @(posedge clk_i) begin
    if (rst_i) trap_handler_addr <= 0;
    else trap_handler_addr <= {csr_mtvec_reg[31:2], 2'd0};
  end

`ifdef RISCV_FORMAL
  // a csr isntruction is a read only if the destination register is not x0
  assign wb_csr_rmask = wb_q_is_csr_read ? 32'hffff_ffff : 0;
  // a csr instruction is a write if its a csrrw or if its (not a csrrw and rs1 != 0)
  assign wb_csr_wmask = wb_q_is_csr_write ? 32'hffff_ffff : 0;
`endif



  //*****************************************************************
  //
  //
  // HAZARD UNIT
  //
  //
  //*****************************************************************

  wire mem_req_stall   ;
  wire load_use_stall  ;
  wire id_wb_rs1_match ;
  wire id_wb_rs2_match ;
  wire id_ex_rs1_match ;
  wire id_ex_rs2_match ;
  wire ex_mem_rs2_match;
  wire ex_mem_rs1_match;
  wire ex_wb_rs2_match ;
  wire ex_wb_rs1_match ;
  wire jump_flush      ;
  assign id_wb_rs1_match  = (id_rs1_addr == wb_q_rd_addr) && |id_rs1_addr;
  assign id_wb_rs2_match  = (id_rs2_addr == wb_q_rd_addr) && |id_rs2_addr;
  assign id_ex_rs1_match  = (id_rs1_addr == ex_q_rd_addr) && |id_rs1_addr;
  assign id_ex_rs2_match  = (id_rs2_addr == ex_q_rd_addr) && |id_rs2_addr;
  assign ex_mem_rs1_match = ((ex_q_rs1_addr == mem_q_rd_addr) && |ex_q_rs1_addr);
  assign ex_mem_rs2_match = ((ex_q_rs2_addr == mem_q_rd_addr) && |ex_q_rs2_addr);
  assign ex_wb_rs1_match  = ((ex_q_rs1_addr == wb_q_rd_addr) && |ex_q_rs1_addr);
  assign ex_wb_rs2_match  = ((ex_q_rs2_addr == wb_q_rd_addr) && |ex_q_rs2_addr);

  /*****************************************/
  //
  //  STALL LOGIC
  //
  /*****************************************/
  // stall if axil transaction is still not done

  // We must stall if a load instruction is in the execute stage while another instruction
  // has a matching source register to that write register in the decode stage
  assign load_use_stall = (ex_q_is_mem_read && (id_ex_rs1_match || id_ex_rs2_match));

  assign mem_req_stall = dmem_periph_req && !mem_done_i;

  /*****************************************/
  //
  //  FORWARDING LOGIC
  //
  /*****************************************/

  //if either source register matches a register we are writing to in a previous
  //instruction we must forward that value from the previous instruction so the updated
  //value is used.
  always @(*) begin
    if (ex_mem_rs1_match && mem_q_is_rd_write) ex_forward_rs1_sel = FORWARD_SEL_MEM_RESULT;
    else if (ex_wb_rs1_match && wb_q_is_rd_write) ex_forward_rs1_sel = FORWARD_SEL_WB_RESULT;
    else ex_forward_rs1_sel = NO_FORWARD_SEL;

    if (ex_mem_rs2_match && mem_q_is_rd_write) ex_forward_rs2_sel = FORWARD_SEL_MEM_RESULT;
    else if (ex_wb_rs2_match && wb_q_is_rd_write) ex_forward_rs2_sel = FORWARD_SEL_WB_RESULT;
    else ex_forward_rs2_sel = NO_FORWARD_SEL;
  end

  assign id_forward_rs1 = id_wb_rs1_match && wb_q_is_rd_write;
  assign id_forward_rs2 = id_wb_rs2_match && wb_q_is_rd_write;

  assign jump_flush = mem_q_jump_taken && !mem_q_is_branch;

  // flush if/id register on a mispredicted branch, a predicted jump, an unconditional jump, or an instruction trap
  // mispredicted branch, jumps, and trapped instruction flushes are unconditional
  // a predicted branch taken flush is conditional so that the branch instruction is not flushed when the next stage is stalled
  assign if_id_flush = mem_branch_mispredict
    || jump_flush
    || (id_predict_btaken && !id_ex_stall && !if_id_stall)
    || (ex_q_trap_valid || mem_q_trap_valid || wb_q_trap_valid);

  // flush id/ex register on a mispredicted branch, a jump, an instruction trap,
  // all flushes are unconditional
  assign id_ex_flush = mem_branch_mispredict
    || jump_flush
    || (mem_q_trap_valid || wb_q_trap_valid);

  // flush ex/mem flush on a mispredicted branch, a jump, an instruction trap,
  // branch mispredict and jumps are conditional flushes to prevent losing the instruction when the next stage is stalled
  // trapped instruction flush is unconditional
  assign ex_mem_flush = (mem_branch_mispredict && !mem_wb_stall)
    || (jump_flush              && !mem_wb_stall)
    || (mem_q_trap_valid || wb_q_trap_valid);

  // flush mem/wb register if a trap instruction is committed, or
  // the previous stage is stalled and the register is not stalled
  assign mem_wb_flush = wb_q_trap_valid;

  // stall the if/id register on a load use hazard, or the next
  // stage is stalled
  assign if_id_stall = load_use_stall
    || id_ex_stall;

  // stall the id/ex register if the next stage is stalled
  assign id_ex_stall = ex_mem_stall;

  // stall the ex/mem register during a memory transaction,
  // or the next stage is stalled
  assign ex_mem_stall = mem_req_stall
    || mem_wb_stall;

  // stall the mem/wb register during a memory transaction
  assign mem_wb_stall = mem_req_stall;

  //*****************************************************************
  //
  //
  // FORMAL VERIFICATION
  //
  //
  //*****************************************************************

`ifdef RISCV_FORMAL

  reg  is_csr_misa      ;
  reg  is_csr_mtvec     ;
  reg  is_csr_mscratch  ;
  reg  is_csr_mepc      ;
  reg  is_csr_mcause    ;
  reg  is_csr_mtval     ;
  reg  is_csr_mcycle    ;
  reg  is_csr_mcycleh   ;
  reg  is_csr_minstret  ;
  reg  is_csr_minstreth ;
  reg  is_csr_mvendorid ;
  reg  is_csr_marchid   ;
  reg  is_csr_mimpid    ;
  reg  is_csr_mhartid   ;
  reg  is_csr_mconfigptr;
  wire rvfi_valid_next  ;
  assign rvfi_valid_next = mem_wb_stall ? 0 : commit_valid;

  always @(*)
    begin
      // PC + instruction flow
      commit_pc_rdata   = wb_q_pc;
      commit_pc_wdata   = wb_q_next_pc;
      commit_insn       = wb_q_insn;
      commit_valid      = wb_q_valid;
      commit_trap_valid = wb_q_trap_valid;
      commit_intr       = wb_q_intr;

      // Register file signals
      commit_rs1_addr  = wb_q_rs1_addr;
      commit_rs2_addr  = wb_q_rs2_addr;
      commit_rd_addr   = wb_q_is_rd_write ? wb_rd_addr : 0;
      commit_rs1_rdata = wb_q_rs1_rdata;
      commit_rs2_rdata = wb_q_rs2_rdata;
      commit_rd_wdata  = wb_q_is_rd_write ? wb_rd_wdata : 0;

      // CSR signals
      commit_csr_addr  = wb_csr_addr;
      commit_csr_wdata = wb_q_csr_wdata;
      commit_csr_wmask = wb_q_is_csr_write ? wb_csr_wmask : 0;
      commit_csr_rdata = wb_q_csr_rdata;
      commit_csr_rmask = wb_q_is_csr_read ? wb_csr_rmask : 0;

      // Memory interface
      commit_mem_addr  = wb_q_mem_addr;
      commit_mem_rmask = wb_q_load_rmask;
      commit_mem_rdata = wb_q_load_rdata;
      commit_mem_wmask = wb_q_store_wmask;
      commit_mem_wdata = wb_q_store_wdata;

      // Trap info
      commit_trap_insn      = wb_q_trap_insn;
      commit_trap_pc        = wb_q_trap_pc;
      commit_trap_next_pc   = wb_q_trap_next_pc;
      commit_trap_rs1_addr  = wb_q_trap_rs1_addr;
      commit_trap_rs2_addr  = wb_q_trap_rs2_addr;
      commit_trap_rd_addr   = wb_q_trap_rd_addr;
      commit_trap_rs1_rdata = wb_q_trap_rs1_rdata;
      commit_trap_rs2_rdata = wb_q_trap_rs2_rdata;
      commit_trap_rd_wdata  = 0;
    end

  always @(*)
    begin
      is_csr_misa       = 0;
      is_csr_mtvec      = 0;
      is_csr_mscratch   = 0;
      is_csr_mepc       = 0;
      is_csr_mcause     = 0;
      is_csr_mtval      = 0;
      is_csr_mcycle     = 0;
      is_csr_mcycleh    = 0;
      is_csr_minstret   = 0;
      is_csr_minstreth  = 0;
      is_csr_mvendorid  = 0;
      is_csr_marchid    = 0;
      is_csr_mimpid     = 0;
      is_csr_mhartid    = 0;
      is_csr_mconfigptr = 0;
      case (commit_csr_addr)
        12'h301 :
          is_csr_misa = 1;
        12'h305 :
          is_csr_mtvec = 1;
        12'h340 :
          is_csr_mscratch = 1;
        12'h341 :
          is_csr_mepc = 1;
        12'h342 :
          is_csr_mcause = 1;
        12'h343 :
          is_csr_mtval = 1;
        12'hB00 :
          is_csr_mcycle = 1;
        12'hb80 :
          is_csr_mcycleh = 1;
        12'hB02 :
          is_csr_minstret = 1;
        12'hb82 :
          is_csr_minstreth = 1;
        12'hf11 :
          is_csr_mvendorid = 1;
        12'hf12 :
          is_csr_marchid = 1;
        12'hf13 :
          is_csr_mimpid = 1;
        12'hf14 :
          is_csr_mhartid = 1;
        12'hf15 :
          is_csr_mconfigptr = 1;
        default :
          ;
      endcase
    end

  always @(posedge clk_i)
    begin
      if (rst_i)
        begin
          rvfi_valid <= 0;
          rvfi_order <= 0;
          rvfi_insn  <= 0;
          rvfi_trap  <= 0;
          rvfi_halt  <= 0;
          rvfi_intr  <= 0;
          rvfi_mode  <= 3;
          rvfi_ixl   <= 1;

          rvfi_rs1_addr  <= 0;
          rvfi_rs2_addr  <= 0;
          rvfi_rs1_rdata <= 0;
          rvfi_rs2_rdata <= 0;

          rvfi_rd_addr  <= 0;
          rvfi_rd_wdata <= 0;

          rvfi_pc_rdata <= 0;
          rvfi_pc_wdata <= 0;

          rvfi_mem_addr  <= 0;
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
        end
      else
        begin
          rvfi_valid <= rvfi_valid_next;
          if (rvfi_valid_next)
            rvfi_order <= rvfi_order + 1;
          rvfi_mode <= 3;
          rvfi_ixl  <= 1;
          rvfi_halt <= 0;
          rvfi_trap <= commit_trap_valid;
          rvfi_intr <= commit_intr;

          if (commit_trap_valid)
            begin
              rvfi_insn      <= commit_trap_insn;
              rvfi_rs1_addr  <= commit_trap_rs1_addr;
              rvfi_rs2_addr  <= commit_trap_rs2_addr;
              rvfi_rs1_rdata <= commit_trap_rs1_rdata;
              rvfi_rs2_rdata <= commit_trap_rs2_rdata;

              rvfi_rd_addr  <= commit_trap_rd_addr;
              rvfi_rd_wdata <= commit_trap_rd_wdata;

              rvfi_pc_rdata <= commit_trap_pc;
              rvfi_pc_wdata <= commit_trap_next_pc;

              rvfi_mem_addr  <= commit_mem_addr;
              rvfi_mem_rmask <= commit_mem_rmask;
              rvfi_mem_wmask <= commit_mem_wmask;
              rvfi_mem_rdata <= commit_mem_rdata;
              rvfi_mem_wdata <= commit_mem_wdata;
            end
          else
            begin
              rvfi_insn      <= commit_insn;
              rvfi_rs1_addr  <= commit_rs1_addr;
              rvfi_rs2_addr  <= commit_rs2_addr;
              rvfi_rs1_rdata <= commit_rs1_rdata;
              rvfi_rs2_rdata <= commit_rs2_rdata;

              rvfi_rd_addr  <= commit_rd_addr;
              rvfi_rd_wdata <= commit_rd_wdata;

              rvfi_pc_rdata <= commit_pc_rdata;
              rvfi_pc_wdata <= commit_trap_valid ? trap_handler_addr : commit_pc_wdata;

              rvfi_mem_addr  <= commit_mem_addr;
              rvfi_mem_rmask <= commit_mem_rmask;
              // shift wmask and wdata if first nonzero bit is not at the lsb
              // riscv formal expects this format
              rvfi_mem_wmask <= commit_mem_wmask;
              rvfi_mem_rdata <= commit_mem_rdata;
              rvfi_mem_wdata <= commit_mem_wdata;
            end


          // make rmask and wmask cleared if an exception
          rvfi_csr_mcycle_wmask <= is_csr_mcycleh ? {commit_csr_wmask, 32'd0} :
            is_csr_mcycle  ? {32'd0, commit_csr_wmask} :
            64'd0;
          rvfi_csr_minstret_wmask <= is_csr_minstreth ? {commit_csr_wmask, 32'd0} :
            is_csr_minstret  ? {32'd0, commit_csr_wmask} :
            64'd0;
          rvfi_csr_mcause_wmask <= is_csr_mcause ? commit_csr_wmask : 32'd0;
          rvfi_csr_mepc_wmask   <= is_csr_mepc ? commit_csr_wmask : 32'd0;
          rvfi_csr_mtvec_wmask  <= is_csr_mtvec ? commit_csr_wmask : 32'd0;
          // csr rmask logic
          rvfi_csr_mcycle_rmask <= is_csr_mcycleh ? {commit_csr_rmask, 32'd0} :
            is_csr_mcycle  ? {32'd0, commit_csr_rmask} :
            64'd0;
          rvfi_csr_minstret_rmask <= is_csr_minstreth ?  {commit_csr_rmask, 32'd0} :
            is_csr_minstret  ? {32'd0, commit_csr_rmask} :
            64'd0;
          rvfi_csr_mcause_rmask <= is_csr_mcause ? commit_csr_rmask : 32'd0;
          rvfi_csr_mtvec_rmask  <= is_csr_mtvec ? commit_csr_rmask : 32'd0;
          rvfi_csr_mepc_rmask   <= is_csr_mepc ? commit_csr_rmask : 32'd0;

          rvfi_csr_mcycle_rdata <= is_csr_mcycleh ? {commit_csr_rdata, 32'd0} :
            is_csr_mcycle  ? {32'd0, commit_csr_rdata} :
            64'd0;
          rvfi_csr_minstret_rdata <= is_csr_minstreth ? {commit_csr_rdata, 32'd0} :
            is_csr_minstret  ? {32'd0, commit_csr_rdata} :
            64'd0;
          // csr rdata logic
          rvfi_csr_mcause_rdata <= is_csr_mcause ? commit_csr_rdata : 32'd0;
          rvfi_csr_mtvec_rdata  <= is_csr_mtvec ? commit_csr_rdata : 32'd0;
          rvfi_csr_mepc_rdata   <= is_csr_mepc ? commit_csr_rdata : 32'd0;

          rvfi_csr_mcycle_wdata <= is_csr_mcycleh ? {commit_csr_wdata, 32'd0} :
            is_csr_mcycle  ? {32'd0, commit_csr_wdata} :
            64'd0;
          rvfi_csr_minstret_wdata <= is_csr_minstreth ? {commit_csr_wdata, 32'd0} :
            is_csr_minstret  ? {32'd0, commit_csr_wdata} :
            64'd0;
          rvfi_csr_mcause_wdata <= is_csr_mcause ? commit_csr_wdata : 32'd0;
          rvfi_csr_mtvec_wdata  <= is_csr_mtvec ? commit_csr_wdata : 32'd0;
          rvfi_csr_mepc_wdata   <= is_csr_mepc ? commit_csr_wdata : 32'd0;

        end
    end

`endif

endmodule
