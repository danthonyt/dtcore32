/////////////////////////////////////////////
//
//  PARAMETERS
//
//
////////////////////////////////////////////
package params_pkg;

  // ALU control signals
  typedef enum logic [3:0] {
    ADD_ALU_CONTROL       = 4'h0,
    SUB_ALU_CONTROL       = 4'h1,
    AND_ALU_CONTROL       = 4'h2,
    OR_ALU_CONTROL        = 4'h3,
    L_SHIFT_ALU_CONTROL   = 4'h4,
    LT_ALU_CONTROL        = 4'h5,
    LTU_ALU_CONTROL       = 4'h6,
    XOR_ALU_CONTROL       = 4'h7,
    R_SHIFT_A_ALU_CONTROL = 4'h8,
    R_SHIFT_L_ALU_CONTROL = 4'h9,
    GE_ALU_CONTROL        = 4'hA,
    GEU_ALU_CONTROL       = 4'hB,
    NE_ALU_CONTROL        = 4'hC,
    JALR_ALU_CONTROL      = 4'hD
  } alu_control_t;

  // Forwarding select
  typedef enum logic [1:0] {
    NO_FORWARD_SEL             = 2'h0,
    FORWARD_SEL_MEM_RESULT = 2'h1,
    FORWARD_SEL_WB_RESULT  = 2'h2
    //FORWARD_SEL_WB_ALU_RESULT  = 2'h3
  } forward_sel_t;


  typedef enum logic [4:0] {
    MEM_NONE = 5'b00000,

    MEM_LB  = 5'b1_0_0_00,  // signed byte
    MEM_LBU = 5'b1_0_1_00,  // unsigned byte
    MEM_LH  = 5'b1_0_0_01,  // signed half
    MEM_LHU = 5'b1_0_1_01,  // unsigned half
    MEM_LW  = 5'b1_0_0_10,  // word (signed/unsigned same)

    MEM_SB = 5'b1_1_0_00,  // store byte
    MEM_SH = 5'b1_1_0_01,  // store half
    MEM_SW = 5'b1_1_0_10   // store word
  } mem_op_t;

  // branch_jump op
  typedef enum logic [1:0] {
    CF_NONE   = 2'b00,
    CF_JUMP   = 2'b01,
    CF_BRANCH = 2'b10,
    CF_JALR   = 2'b11
  } cf_op_t;

  // branch_jump op
  typedef enum logic [2:0] {
    CSR_NONE  = 3'b00,
    CSR_READ  = 3'b01,
    CSR_WRITE = 3'b10,
    CSR_SET   = 3'b11,
    CSR_CLEAR = 3'b100
  } csr_op_t;

  typedef enum logic [2:0] {
    I_ALU_TYPE = 3'b000,
    S_TYPE = 3'b001,
    B_TYPE = 3'b010,
    J_TYPE = 3'b011,
    I_SHIFT_TYPE = 3'b100,
    U_TYPE = 3'b101,
    CSR_TYPE = 3'b110
  } imm_ext_op_t;


  // EX stage ALU A select
  typedef enum logic [1:0] {
    ALU_A_SEL_REG_DATA = 2'b00,
    ALU_A_SEL_ZERO     = 2'b01,
    ALU_A_SEL_PC       = 2'b10
  } alu_a_sel_t;

  // EX stage ALU B select
  typedef enum logic {
    ALU_B_SEL_REG_DATA = 1'b0,
    ALU_B_SEL_IMM      = 1'b1
  } alu_b_sel_t;

  // EX stage ALU operation
  typedef enum logic [1:0] {
    ALU_OP_ILOAD_S_U_TYPE     = 2'b00,
    ALU_OP_B_TYPE             = 2'b01,
    ALU_OP_IALU_ISHIFT_R_TYPE = 2'b10,
    ALU_OP_JALR               = 2'b11
  } alu_op_t;

  // EX stage PC target ALU select
  typedef enum logic {
    PC_ALU_SEL_PC       = 1'b0,
    PC_ALU_SEL_REG_DATA = 1'b1
  } pc_alu_sel_t;

  // EX stage CSR operand select
  typedef enum logic {
    CSR_BITMASK_SEL_REG_DATA = 1'b0,
    CSR_BITMASK_SEL_IMM      = 1'b1
  } csr_bitmask_sel_t;


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
`ifdef RISCV_FORMAL

  typedef struct packed {
    logic [31:0] insn;
    logic [31:0] pc;
    logic [31:0] next_pc;
    logic [4:0]  rs1_addr;
    logic [4:0]  rs2_addr;
    logic [4:0]  rd_addr;
    logic [31:0] rs1_rdata;
    logic [31:0] rs2_rdata;
    logic [31:0] rd_wdata;
  } trap_info_t;

  typedef struct packed {
    logic [31:0] pc_rdata;
    logic [31:0] pc_wdata;
    logic [31:0] insn;
    logic        valid;
    logic trap_valid;
    logic        intr;
    logic [4:0]  rs1_addr;
    logic [4:0]  rs2_addr;
    logic [4:0]  rd_addr;
    logic [31:0] rs1_rdata;
    logic [31:0] rs2_rdata;
    logic [31:0] rd_wdata;
    logic [11:0] csr_addr;
    logic [31:0] csr_wdata;
    logic [3:0]  csr_wmask;
    logic [31:0] csr_rdata;
    logic [3:0]  csr_rmask;
    logic [31:0] mem_addr;
    logic [3:0]  mem_rmask;
    logic [31:0] mem_rdata;
    logic [3:0]  mem_wmask;
    logic [31:0] mem_wdata;
    trap_info_t  rvfi_trap_info;
  } rvfi_t;
`endif

  typedef struct packed {
    logic        valid;
    logic [31:0] pc;
    logic [31:0] pc_plus_4;
    logic [31:0] insn;
`ifdef RISCV_FORMAL
    logic        intr;
`endif

  } if_id_t;

  typedef struct packed {
    logic             valid;
    logic [31:0]      pc;
    logic [31:0]      pc_plus_4;
    logic [4:0]       rs1_addr;
    logic [4:0]       rs2_addr;
    logic [4:0]       rd_addr;
    logic [31:0]      rs1_rdata;
    logic [31:0]      rs2_rdata;
    logic [31:0]      imm_ext;
    logic [11:0]      csr_addr;
    logic [31:0]      csr_rdata;
    csr_op_t          csr_op;
    cf_op_t           cf_op;
    alu_control_t     alu_control;
    alu_a_sel_t       alu_a_sel;
    alu_b_sel_t       alu_b_sel;
    pc_alu_sel_t      pc_alu_sel;
    csr_bitmask_sel_t csr_bitmask_sel;
    mem_op_t          mem_op;
    logic             trap_valid;
    logic [31:0]      trap_mcause;
    logic [31:0]      trap_pc;
`ifdef RISCV_FORMAL
    logic [31:0]      insn;
    logic             intr;
    trap_info_t       rvfi_trap_info;
`endif
  } id_ex_t;

  typedef struct packed {
    logic        valid;
    logic [31:0] pc;
    logic [31:0] pc_plus_4;
    logic [4:0]  rd_addr;
    logic [11:0] csr_addr;
    logic [31:0] csr_wdata;
    mem_op_t     mem_op;
    cf_op_t           cf_op;
    logic [31:0] store_wdata;
    logic [31:0] alu_csr_result;
    logic        trap_valid;
    logic [31:0] trap_mcause;
    logic [31:0] trap_pc;
    logic branch_cond;
    logic jump_taken;
    logic jaddr;
`ifdef RISCV_FORMAL
    logic [31:0] next_pc;
    logic [31:0] insn;
    logic        intr;
    logic [31:0] csr_rdata;
    logic [4:0]  rs1_addr;
    logic [4:0]  rs2_addr;
    logic [31:0] rs1_rdata;
    logic [31:0] rs2_rdata;
    trap_info_t  rvfi_trap_info;
`endif
  } ex_mem_t;

  typedef struct packed {
    logic        valid;
    logic [4:0]  rd_addr;
    logic [11:0] csr_addr;
    logic [31:0] csr_wdata;
    logic [31:0] rd_wdata;
    logic        trap_valid;
    logic [31:0] trap_mcause;
    logic [31:0] trap_pc;
`ifdef RISCV_FORMAL
    logic [31:0] pc;
    logic [31:0] pc_plus_4;
    logic [31:0] next_pc;
    logic [31:0] insn;
    logic        intr;
    logic [31:0] csr_rdata;
    logic [31:0] mem_addr;
    logic [31:0] load_rdata;
    logic [4:0]  rs1_addr;
    logic [4:0]  rs2_addr;
    logic [31:0] rs1_rdata;
    logic [31:0] rs2_rdata;
    logic [3:0]  load_rmask;
    logic [3:0]  store_wmask;
    logic [31:0] store_wdata;
    trap_info_t  rvfi_trap_info;
`endif
  } mem_wb_t;
  
  function automatic id_ex_t reset_id_ex();
    reset_id_ex = '{
        default: '0,
        `ifdef RISCV_FORMAL
        insn: NOP_INSTRUCTION,
        rvfi_trap_info: trap_info_t'('0),
        `endif
        csr_op: csr_op_t'('0),
        cf_op_t: cf_op_t'('0),
        alu_control: alu_control_t'('0),
        alu_a_sel: alu_a_sel_t'('0),
        alu_b_sel: alu_b_sel_t'('0),
        pc_alu_sel: pc_alu_sel_t'('0),
        csr_bitmask_sel: csr_bitmask_sel_t'('0),
        //result_sel: result_sel_t'('0),
        mem_op: mem_op_t'('0)
    };
  endfunction

  function automatic ex_mem_t reset_ex_mem();
    reset_ex_mem = '{
        default: '0,
        `ifdef RISCV_FORMAL
        insn: NOP_INSTRUCTION,
        rvfi_trap_info: trap_info_t'('0),
        `endif
        //result_sel: result_sel_t'('0),
        cf_op: cf_op_t'(0),
        mem_op: mem_op_t'(0)
    };
  endfunction

  function automatic mem_wb_t reset_mem_wb();
    reset_mem_wb = '{
        default: '0
        `ifdef RISCV_FORMAL
        ,
        insn: NOP_INSTRUCTION,
        rvfi_trap_info: trap_info_t'('0)
        `endif
        //result_sel: result_sel_t'('0)
    };
  endfunction

endpackage
