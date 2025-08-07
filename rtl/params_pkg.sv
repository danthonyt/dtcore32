/////////////////////////////////////////////
//
//  PARAMETERS
//
//
////////////////////////////////////////////
package params_pkg;


  typedef struct {
    logic valid;
    logic is_interrupt;
    logic [31:0] insn;
    logic [30:0] mcause;
    logic [31:0] pc;
  } trap_info_t;

  localparam logic [3:0] ADD_ALU_CONTROL = 4'h0;
  localparam logic [3:0] SUB_ALU_CONTROL = 4'h1;
  localparam logic [3:0] AND_ALU_CONTROL = 4'h2;
  localparam logic [3:0] OR_ALU_CONTROL = 4'h3;
  localparam logic [3:0] L_SHIFT_ALU_CONTROL = 4'h4;
  localparam logic [3:0] LT_ALU_CONTROL = 4'h5;
  localparam logic [3:0] LTU_ALU_CONTROL = 4'h6;
  localparam logic [3:0] XOR_ALU_CONTROL = 4'h7;
  localparam logic [3:0] R_SHIFT_A_ALU_CONTROL = 4'h8;
  localparam logic [3:0] R_SHIFT_L_ALU_CONTROL = 4'h9;
  localparam logic [3:0] GE_ALU_CONTROL = 4'hA;
  localparam logic [3:0] GEU_ALU_CONTROL = 4'hB;
  localparam logic [3:0] BNE_ALU_CONTROL = 4'hC;
  localparam logic [3:0] NE_ALU_CONTROL = 4'hC;
  
  

  localparam logic [2:0] FORWARD_SEL_NO_FORWARD = 3'h0;
  localparam logic [2:0] FORWARD_SEL_MEM1_ALU_RESULT = 3'h1;
  localparam logic [2:0] FORWARD_SEL_MEM2_ALU_RESULT = 3'h2;
  localparam logic [2:0] FORWARD_SEL_MEM2_MEM_RDATA = 3'h3;
  localparam logic [2:0] FORWARD_SEL_WB_RESULT = 3'h4;



  localparam logic REGFILE_WRITE_ENABLE = 1'b1;

  // extended immediate source types used by different instructions
  localparam logic [2:0] I_ALU_TYPE_IMM_SRC = 3'b000;
  localparam logic [2:0] S_TYPE_IMM_SRC = 3'b001;
  localparam logic [2:0] B_TYPE_IMM_SRC = 3'b010;
  localparam logic [2:0] J_TYPE_IMM_SRC = 3'b011;
  localparam logic [2:0] I_SHIFT_TYPE_IMM_SRC = 3'b100;
  localparam logic [2:0] U_TYPE_IMM_SRC = 3'b101;
  localparam logic [2:0] CSR_TYPE_IMM_SRC = 3'b110;

  //ID_alu_a_src
  localparam logic [1:0] ALU_A_SRC_SELECT_REG_DATA = 2'b00;
  localparam logic [1:0] ALU_A_SRC_SELECT_ZERO = 2'b01;
  localparam logic [1:0] ALU_A_SRC_SELECT_PC = 2'b10;

  //ID_alu_b_src
  localparam logic ALU_B_SRC_SELECT_REG_DATA = 1'b0;
  localparam logic ALU_B_SRC_SELECT_IMM = 1'b1;

  //ID_mem_wr_size
  localparam logic [1:0] MEM_NO_DMEM_WR = 2'h0;
  localparam logic [1:0] MEM_WORD_WR = 2'h1;
  localparam logic [1:0] MEM_HALF_WR = 2'h2;
  localparam logic [1:0] MEM_BYTE_WR = 2'h3;

  //ID_result_src
  localparam logic [1:0] RESULT_SRC_SELECT_ALU_RESULT = 2'b00;
  localparam logic [1:0] RESULT_SRC_SELECT_DMEM_RD_DATA = 2'b01;
  localparam logic [1:0] RESULT_SRC_SELECT_NEXT_INSTR_ADDR = 2'b10;
  localparam logic [1:0] RESULT_SRC_SELECT_CSR_READ_DATA = 2'b11;

  //ID_branch
  localparam logic IS_BRANCH_INSTR = 1'b1;
  localparam logic IS_NOT_BRANCH_INSTR = 1'b0;

  //ID_alu_op
  localparam logic [1:0] ALU_OP_ILOAD_S_U_TYPE = 2'b00;
  localparam logic [1:0] ALU_OP_B_TYPE = 2'b01;
  localparam logic [1:0] ALU_OP_IALU_ISHIFT_R_TYPE = 2'b10;

  //ID_jump
  localparam logic IS_JUMP_INSTR = 1'b1;
  localparam logic IS_NOT_JUMP_INSTR = 1'b0;

  //ID_load_size
  localparam logic [2:0] DMEM_LOAD_SIZE_NO_LOAD = 3'b000;
  localparam logic [2:0] DMEM_LOAD_SIZE_WORD = 3'b001;
  localparam logic [2:0] DMEM_LOAD_SIZE_HALF = 3'b010;
  localparam logic [2:0] DMEM_LOAD_SIZE_HALFU = 3'b011;
  localparam logic [2:0] DMEM_LOAD_SIZE_BYTE = 3'b100;
  localparam logic [2:0] DMEM_LOAD_SIZE_BYTEU = 3'b101;

  //ID_pc_target_alu_src
  localparam logic PC_TARGET_ALU_SRC_SELECT_PC = 1'b0;
  localparam logic PC_TARGET_ALU_SRC_SELECT_REG_DATA = 1'b1;

  // ID_csr_wr_type
  localparam logic [1:0] CSR_WRITE_DISABLE = 2'b00;
  localparam logic [1:0] CSR_WRITE_RAW_VALUE = 2'b01;
  localparam logic [1:0] CSR_WRITE_SET_BIT_MASK = 2'b10;
  localparam logic [1:0] CSR_WRITE_CLEAR_BIT_MASK = 2'b11;

  // ID_csr_wr_operand_src
  localparam logic CSR_SRC_SELECT_REG_DATA = 1'b0;
  localparam logic CSR_SRC_SELECT_IMM = 1'b1;

  // OPCODES
  localparam logic [6:0] OPCODE_LOAD = 7'b0000011;
  localparam logic [6:0] OPCODE_STORE = 7'b0100011;
  localparam logic [6:0] OPCODE_R_TYPE = 7'b0110011;
  localparam logic [6:0] OPCODE_B_TYPE = 7'b1100011;
  localparam logic [6:0] OPCODE_I_TYPE = 7'b0010011;
  localparam logic [6:0] OPCODE_JAL = 7'b1101111;
  localparam logic [6:0] OPCODE_U_TYPE_LUI = 7'b0110111;
  localparam logic [6:0] OPCODE_U_TYPE_AUIPC = 7'b0010111;
  localparam logic [6:0] OPCODE_JALR = 7'b1100111;
  localparam logic [6:0] OPCODE_SYSCALL_CSR = 7'b1110011;
  // FUNCT3
  localparam logic [2:0] FUNCT3_LB = 3'b000;
  localparam logic [2:0] FUNCT3_LH = 3'b001;
  localparam logic [2:0] FUNCT3_LW = 3'b010;
  localparam logic [2:0] FUNCT3_LBU = 3'b100;
  localparam logic [2:0] FUNCT3_LHU = 3'b101;

  localparam logic [2:0] FUNCT3_SB = 3'b000;
  localparam logic [2:0] FUNCT3_SH = 3'b001;
  localparam logic [2:0] FUNCT3_SW = 3'b010;

  localparam logic [2:0] FUNCT3_BEQ = 3'b000;
  localparam logic [2:0] FUNCT3_BNE = 3'b001;
  localparam logic [2:0] FUNCT3_BLT = 3'b100;
  localparam logic [2:0] FUNCT3_BGE = 3'b101;
  localparam logic [2:0] FUNCT3_BLTU = 3'b110;
  localparam logic [2:0] FUNCT3_BGEU = 3'b111;

  localparam logic [2:0] FUNCT3_ADD = 3'b000;
  localparam logic [2:0] FUNCT3_SUB = 3'b000;
  localparam logic [2:0] FUNCT3_SLL = 3'b001;
  localparam logic [2:0] FUNCT3_SLT = 3'b010;
  localparam logic [2:0] FUNCT3_SLTU_SLTIU = 3'b011;
  localparam logic [2:0] FUNCT3_XOR = 3'b100;
  localparam logic [2:0] FUNCT3_SRA = 3'b101;
  localparam logic [2:0] FUNCT3_SRL = 3'b101;
  localparam logic [2:0] FUNCT3_SRLI = 3'b101;
  localparam logic [2:0] FUNCT3_SRAI = 3'b101;
  localparam logic [2:0] FUNCT3_SLLI = 3'b001;
  localparam logic [2:0] FUNCT3_OR = 3'b110;
  localparam logic [2:0] FUNCT3_AND = 3'b111;

  localparam logic [2:0] FUNCT3_ECALL_EBREAK = 3'b000;

  localparam logic [2:0] FUNCT3_CSRRW = 3'b001;
  localparam logic [2:0] FUNCT3_CSRRS = 3'b010;
  localparam logic [2:0] FUNCT3_CSRRC = 3'b011;
  localparam logic [2:0] FUNCT3_CSRRWI = 3'b101;
  localparam logic [2:0] FUNCT3_CSRRSI = 3'b110;
  localparam logic [2:0] FUNCT3_CSRRCI = 3'b111;
  // FUNCT7
  localparam logic [6:0] FUNCT7_ADD = 7'h00;
  localparam logic [6:0] FUNCT7_SUB = 7'h20;
  localparam logic [6:0] FUNCT7_SLL = 7'h00;
  localparam logic [6:0] FUNCT7_SLT = 7'h00;

  localparam logic [6:0] FUNCT7_SLTU = 7'h00;
  localparam logic [6:0] FUNCT7_XOR = 7'h00;
  localparam logic [6:0] FUNCT7_SRL = 7'h00;
  localparam logic [6:0] FUNCT7_SRA = 7'h20;
  localparam logic [6:0] FUNCT7_OR = 7'h00;
  localparam logic [6:0] FUNCT7_AND = 7'h00;

  localparam logic [6:0] FUNCT7_SLLI = 7'h00;
  localparam logic [6:0] FUNCT7_SRLI = 7'h00;
  localparam logic [6:0] FUNCT7_SRAI = 7'h20;

  // FUNCT12
  localparam logic [6:0] FUNCT12_ECALL = 12'h000;
  localparam logic [6:0] FUNCT12_EBREAK = 12'h001;

  // Exception types
  localparam logic [30:0] TRAP_CODE_INSTR_ADDR_MISALIGNED = 31'd0;
  localparam logic [30:0] TRAP_CODE_ILLEGAL_INSTR = 31'd2;
  localparam logic [30:0] TRAP_CODE_BREAKPOINT = 31'd3;
  localparam logic [30:0] TRAP_CODE_LOAD_ADDR_MISALIGNED = 31'd4;
  localparam logic [30:0] TRAP_CODE_STORE_ADDR_MISALIGNED = 31'd6;
  localparam logic [30:0] TRAP_CODE_ECALL_M_MODE = 31'd11;


  localparam logic [31:0] NOP_INSTRUCTION = 32'h00000013;  // addi x0, x0, 0

  localparam logic [11:0] CSR_ADDR_MSTATUS = 12'h300;
  localparam logic [11:0] CSR_ADDR_MISA = 12'h301;
  localparam logic [11:0] CSR_ADDR_MIE = 12'h304;
  localparam logic [11:0] CSR_ADDR_MTVEC = 12'h305;
  localparam logic [11:0] CSR_ADDR_MSCRATCH = 12'h340;
  localparam logic [11:0] CSR_ADDR_MEPC = 12'h341;
  localparam logic [11:0] CSR_ADDR_MCAUSE = 12'h342;
  localparam logic [11:0] CSR_ADDR_MTVAL = 12'h343;
  localparam logic [11:0] CSR_ADDR_MIP = 12'h344;
  localparam logic [11:0] CSR_ADDR_MCYCLE = 12'hB00;
  localparam logic [11:0] CSR_ADDR_MCYCLEH = 12'hB80;
  localparam logic [11:0] CSR_ADDR_MINSTRET = 12'hB02;
  localparam logic [11:0] CSR_ADDR_MINSTRETH = 12'hB82;
  localparam logic [11:0] CSR_ADDR_MVENDORID = 12'hF11;
  localparam logic [11:0] CSR_ADDR_MARCHID = 12'hF12;
  localparam logic [11:0] CSR_ADDR_MIMPID = 12'hF13;
  localparam logic [11:0] CSR_ADDR_MHARTID = 12'hF14;
  localparam logic [11:0] CSR_ADDR_MCONFIGPTR = 12'hF15;
  localparam logic [11:0] CSR_ADDR_NO_ADDR = 12'h000;

endpackage
