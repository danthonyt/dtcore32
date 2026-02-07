package riscv_pkg;
`define RISCV_FORMAL
//-------------------------------
// Widths for pseudo-types
//-------------------------------
  parameter  FWD_SEL_T_WIDTH         = 2;
  parameter  IMM_EXT_OP_T_WIDTH      = 3;
  parameter  ALU_CTRL_T_WIDTH        = 4;
  parameter  ALU_A_SEL_T_WIDTH       = 2;
  parameter  ALU_B_SEL_T_WIDTH       = 1;
  parameter  ALU_OP_T_WIDTH          = 2;
  parameter  PC_ALU_SEL_T_WIDTH      = 1;
  parameter  CSR_BITMASK_SEL_T_WIDTH = 1;


//-------------------------------
// ALU Control Signals
//-------------------------------
  parameter  [3:0] ADD_ALU_CONTROL       = 4'h0;
  parameter  [3:0] SUB_ALU_CONTROL       = 4'h1;
  parameter  [3:0] AND_ALU_CONTROL       = 4'h2;
  parameter  [3:0] OR_ALU_CONTROL        = 4'h3;
  parameter  [3:0] L_SHIFT_ALU_CONTROL   = 4'h4;
  parameter  [3:0] LT_ALU_CONTROL        = 4'h5;
  parameter  [3:0] LTU_ALU_CONTROL       = 4'h6;
  parameter  [3:0] XOR_ALU_CONTROL       = 4'h7;
  parameter  [3:0] R_SHIFT_A_ALU_CONTROL = 4'h8;
  parameter  [3:0] R_SHIFT_L_ALU_CONTROL = 4'h9;
  parameter  [3:0] GE_ALU_CONTROL        = 4'hA;
  parameter  [3:0] GEU_ALU_CONTROL       = 4'hB;
  parameter  [3:0] NE_ALU_CONTROL        = 4'hC;
  parameter  [3:0] JALR_ALU_CONTROL      = 4'hD;

//-------------------------------
// Forwarding select
//-------------------------------
  parameter  [1:0] NO_FORWARD_SEL         = 2'h0;
  parameter  [1:0] FORWARD_SEL_MEM_RESULT = 2'h1;
  parameter  [1:0] FORWARD_SEL_WB_RESULT  = 2'h2;

//-------------------------------
// Immediate type
//-------------------------------
  parameter  [2:0]
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
  parameter  [1:0] ALU_A_SEL_REG_DATA = 2'b00;
  parameter  [1:0] ALU_A_SEL_ZERO     = 2'b01;
  parameter  [1:0] ALU_A_SEL_PC       = 2'b10;

//-------------------------------
// ALU B select
//-------------------------------
  parameter  ALU_B_SEL_REG_DATA = 1'b0;
  parameter  ALU_B_SEL_IMM      = 1'b1;

//-------------------------------
// ALU Operation type
//-------------------------------
  parameter  [1:0]
    ALU_OP_ILOAD_S_U_TYPE     = 2'b00,
    ALU_OP_B_TYPE             = 2'b01,
    ALU_OP_IALU_ISHIFT_R_TYPE = 2'b10,
    ALU_OP_JALR               = 2'b11;


//-------------------------------
// PC ALU select
//-------------------------------
  parameter  PC_ALU_SEL_PC       = 1'b0;
  parameter  PC_ALU_SEL_REG_DATA = 1'b1;

//-------------------------------
// CSR bitmask select
//-------------------------------
  parameter  CSR_BITMASK_SEL_REG_DATA = 1'b0;
  parameter  CSR_BITMASK_SEL_IMM      = 1'b1;

//-------------------------------
// Opcodes
//-------------------------------
  parameter  [6:0] OPCODE_LOAD         = 7'b0000011;
  parameter  [6:0] OPCODE_STORE        = 7'b0100011;
  parameter  [6:0] OPCODE_R_TYPE       = 7'b0110011;
  parameter  [6:0] OPCODE_B_TYPE       = 7'b1100011;
  parameter  [6:0] OPCODE_I_TYPE       = 7'b0010011;
  parameter  [6:0] OPCODE_JAL          = 7'b1101111;
  parameter  [6:0] OPCODE_U_TYPE_LUI   = 7'b0110111;
  parameter  [6:0] OPCODE_U_TYPE_AUIPC = 7'b0010111;
  parameter  [6:0] OPCODE_JALR         = 7'b1100111;
  parameter  [6:0] OPCODE_SYSCALL_CSR  = 7'b1110011;

//-------------------------------
// Funct3 codes
//-------------------------------
  parameter  [2:0] FUNCT3_LB  = 3'b000;
  parameter  [2:0] FUNCT3_LH  = 3'b001;
  parameter  [2:0] FUNCT3_LW  = 3'b010;
  parameter  [2:0] FUNCT3_LBU = 3'b100;
  parameter  [2:0] FUNCT3_LHU = 3'b101;

  parameter  [2:0] FUNCT3_SB = 3'b000;
  parameter  [2:0] FUNCT3_SH = 3'b001;
  parameter  [2:0] FUNCT3_SW = 3'b010;

  parameter  [2:0] FUNCT3_BEQ  = 3'b000;
  parameter  [2:0] FUNCT3_BNE  = 3'b001;
  parameter  [2:0] FUNCT3_BLT  = 3'b100;
  parameter  [2:0] FUNCT3_BGE  = 3'b101;
  parameter  [2:0] FUNCT3_BLTU = 3'b110;
  parameter  [2:0] FUNCT3_BGEU = 3'b111;

  parameter  [2:0] FUNCT3_ADD        = 3'b000;
  parameter  [2:0] FUNCT3_SUB        = 3'b000;
  parameter  [2:0] FUNCT3_SLL        = 3'b001;
  parameter  [2:0] FUNCT3_SLT        = 3'b010;
  parameter  [2:0] FUNCT3_SLTU_SLTIU = 3'b011;
  parameter  [2:0] FUNCT3_XOR        = 3'b100;
  parameter  [2:0] FUNCT3_SRA        = 3'b101;
  parameter  [2:0] FUNCT3_SRL        = 3'b101;
  parameter  [2:0] FUNCT3_SRLI       = 3'b101;
  parameter  [2:0] FUNCT3_SRAI       = 3'b101;
  parameter  [2:0] FUNCT3_SLLI       = 3'b001;
  parameter  [2:0] FUNCT3_OR         = 3'b110;
  parameter  [2:0] FUNCT3_AND        = 3'b111;

  parameter  [2:0] FUNCT3_ECALL_EBREAK = 3'b000;
  parameter  [2:0] FUNCT3_CSRRW        = 3'b001;
  parameter  [2:0] FUNCT3_CSRRS        = 3'b010;
  parameter  [2:0] FUNCT3_CSRRC        = 3'b011;
  parameter  [2:0] FUNCT3_CSRRWI       = 3'b101;
  parameter  [2:0] FUNCT3_CSRRSI       = 3'b110;
  parameter  [2:0] FUNCT3_CSRRCI       = 3'b111;

//-------------------------------
// Funct7 codes
//-------------------------------
  parameter  [6:0] FUNCT7_ADD  = 7'h00;
  parameter  [6:0] FUNCT7_SUB  = 7'h20;
  parameter  [6:0] FUNCT7_SLL  = 7'h00;
  parameter  [6:0] FUNCT7_SLT  = 7'h00;
  parameter  [6:0] FUNCT7_SLTU = 7'h00;
  parameter  [6:0] FUNCT7_XOR  = 7'h00;
  parameter  [6:0] FUNCT7_SRL  = 7'h00;
  parameter  [6:0] FUNCT7_SRA  = 7'h20;
  parameter  [6:0] FUNCT7_OR   = 7'h00;
  parameter  [6:0] FUNCT7_AND  = 7'h00;
  parameter  [6:0] FUNCT7_SLLI = 7'h00;
  parameter  [6:0] FUNCT7_SRLI = 7'h00;
  parameter  [6:0] FUNCT7_SRAI = 7'h20;

//-------------------------------
// Funct12 codes
//-------------------------------
  parameter  [11:0] FUNCT12_ECALL  = 12'h000;
  parameter  [11:0] FUNCT12_EBREAK = 12'h001;

//-------------------------------
// Exception codes / trap codes
//-------------------------------
  parameter  [30:0] TRAP_CODE_INSTR_ADDR_MISALIGNED = 31'd0 ;
  parameter  [30:0] TRAP_CODE_ILLEGAL_INSTR         = 31'd2 ;
  parameter  [30:0] TRAP_CODE_BREAKPOINT            = 31'd3 ;
  parameter  [30:0] TRAP_CODE_LOAD_ADDR_MISALIGNED  = 31'd4 ;
  parameter  [30:0] TRAP_CODE_STORE_ADDR_MISALIGNED = 31'd6 ;
  parameter  [30:0] TRAP_CODE_ECALL_M_MODE          = 31'd11;

//-------------------------------
// NOP instruction
//-------------------------------
  parameter  [31:0] NOP_INSTRUCTION = 32'h00000013;

//-------------------------------
// CSR Addresses
//-------------------------------
  parameter  [11:0] CSR_ADDR_MSTATUS    = 12'h300;
  parameter  [11:0] CSR_ADDR_MISA       = 12'h301;
  parameter  [11:0] CSR_ADDR_MIE        = 12'h304;
  parameter  [11:0] CSR_ADDR_MTVEC      = 12'h305;
  parameter  [11:0] CSR_ADDR_MSCRATCH   = 12'h340;
  parameter  [11:0] CSR_ADDR_MEPC       = 12'h341;
  parameter  [11:0] CSR_ADDR_MCAUSE     = 12'h342;
  parameter  [11:0] CSR_ADDR_MTVAL      = 12'h343;
  parameter  [11:0] CSR_ADDR_MIP        = 12'h344;
  parameter  [11:0] CSR_ADDR_MCYCLE     = 12'hB00;
  parameter  [11:0] CSR_ADDR_MCYCLEH    = 12'hB80;
  parameter  [11:0] CSR_ADDR_MINSTRET   = 12'hB02;
  parameter  [11:0] CSR_ADDR_MINSTRETH  = 12'hB82;
  parameter  [11:0] CSR_ADDR_MVENDORID  = 12'hF11;
  parameter  [11:0] CSR_ADDR_MARCHID    = 12'hF12;
  parameter  [11:0] CSR_ADDR_MIMPID     = 12'hF13;
  parameter  [11:0] CSR_ADDR_MHARTID    = 12'hF14;
  parameter  [11:0] CSR_ADDR_MCONFIGPTR = 12'hF15;
  parameter  [11:0] CSR_ADDR_NO_ADDR    = 12'h000;

  parameter  RESET_PC = 32'd0;
endpackage