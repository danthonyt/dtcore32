import riscv_pkg::*;
module maindec (
  input  logic [                        6:0] id_op             ,
  input  logic [                        2:0] id_funct3         ,
  input  logic [                        6:0] id_funct7         ,
  input  logic [                       11:0] id_funct12        ,
  input  logic [                        4:0] id_rs1_addr       ,
  input  logic [                        4:0] id_rd_addr        ,
  output logic                               ecall_m_trap      ,
  output logic                               illegal_instr_trap,
  output logic                               breakpoint_trap   ,
  // valid registers
  output logic                               is_rd_write       ,
  output logic                               is_rs1_read       ,
  output logic                               is_rs2_read       ,
  // mux select signals
  output logic [         ALU_OP_T_WIDTH-1:0] alu_op            ,
  // control signals
  output logic                               is_branch         ,
  output logic                               is_jump           ,
  output logic                               is_jal            ,
  output logic                               is_jalr           ,
  output logic                               is_csr_write      ,
  output logic                               is_csr_read       ,
  output logic                               csr_op_rw         ,
  output logic                               csr_op_clear      ,
  output logic                               csr_op_set        ,
  output logic                               is_mem_write      ,
  output logic                               is_mem_read       ,
  output logic                               is_memsize_b      ,
  output logic                               is_memsize_bu     ,
  output logic                               is_memsize_h      ,
  output logic                               is_memsize_hu     ,
  output logic                               is_memsize_w      ,
  // sources
  output logic [     IMM_EXT_OP_T_WIDTH-1:0] imm_ext_op        ,
  output logic [      ALU_A_SEL_T_WIDTH-1:0] alu_a_src         ,
  output logic [      ALU_B_SEL_T_WIDTH-1:0] alu_b_src         ,
  output logic [     PC_ALU_SEL_T_WIDTH-1:0] pc_alu_src        ,
  output logic [CSR_BITMASK_SEL_T_WIDTH-1:0] csr_bitmask_sel
);
  logic is_itype              ;
  logic is_rtype              ;
  logic is_SRAI_funct3        ;
  logic is_SRA_or_SUB_funct3  ;
  logic is_SLLI_or_SRLI_funct3;
  logic is_shift_itype        ;
  logic is_unknown_rtype      ;
  logic is_unknown_itype      ;

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

endmodule