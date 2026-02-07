package riscv_pkg;
`define RISCV_FORMAL
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
endpackage