`include "formal_defs.svh"
import riscv_pkg::*;
module ex_stage (
  // Clock & Reset
  input  logic        clk_i               ,
  input  logic        rst_i               ,
  // Pipeline inputs
  input  logic        ex_q_valid          ,
  input  logic [31:0] ex_q_pc             ,
  input  logic [31:0] ex_q_pc_plus_4      ,
  input  logic [31:0] ex_q_rs1_rdata      ,
  input  logic [31:0] ex_q_rs2_rdata      ,
  input  logic [ 4:0] ex_q_rs1_addr       ,
  input  logic [ 4:0] ex_q_rs2_addr       ,
  input  logic [ 4:0] ex_q_rd_addr        ,
  input  logic        ex_q_is_rd_write    ,
  input  logic [ 5:0] ex_q_pht_idx        ,
  input  logic        ex_q_is_csr_write   ,
  input  logic        ex_q_is_csr_read    ,
  input  logic [11:0] ex_q_csr_addr       ,
  input  logic [31:0] ex_q_csr_rdata      ,
  input  logic [31:0] ex_q_imm_ext        ,
  input  logic [31:0] ex_q_insn           ,
  input  logic        ex_q_intr           ,
  input  logic        ex_q_is_jump        ,
  input  logic        ex_q_is_jal         ,
  input  logic        ex_q_is_jalr        ,
  input  logic        ex_q_is_branch      ,
  input  logic        ex_q_branch_predict ,
  input  logic [ 3:0] ex_q_alu_control    ,
  input  logic [ 1:0] ex_q_alu_a_sel      ,
  input  logic        ex_q_alu_b_sel      ,
  input  logic        ex_q_pc_alu_sel     ,
  input  logic        ex_q_csr_bitmask_sel,
  input  logic        ex_q_csr_op_rw      ,
  input  logic        ex_q_csr_op_set     ,
  input  logic        ex_q_csr_op_clear   ,
  input  logic        ex_q_is_mem_read    ,
  input  logic        ex_q_is_mem_write   ,
  input  logic        ex_q_is_memsize_b   ,
  input  logic        ex_q_is_memsize_bu  ,
  input  logic        ex_q_is_memsize_h   ,
  input  logic        ex_q_is_memsize_hu  ,
  input  logic        ex_q_is_memsize_w   ,
  input  logic        ex_q_trap_valid     ,
  input  logic [31:0] ex_q_trap_pc        ,
  input  logic [31:0] ex_q_trap_mcause    ,
  input  logic [31:0] ex_q_trap_insn      ,
  input  logic [31:0] ex_q_trap_next_pc   ,
  input  logic [ 4:0] ex_q_trap_rs1_addr  ,
  input  logic [ 4:0] ex_q_trap_rs2_addr  ,
  input  logic [ 4:0] ex_q_trap_rd_addr   ,
  input  logic [31:0] ex_q_trap_rs1_rdata ,
  input  logic [31:0] ex_q_trap_rs2_rdata ,
  input  logic [31:0] ex_q_trap_rd_wdata  ,
  // Forwarding inputs
  input  logic [31:0] mem_q_alu_csr_result,
  input  logic [31:0] wb_rd_wdata         ,
  input  logic [ 1:0] ex_forward_rs1_sel  ,
  input  logic [ 1:0] ex_forward_rs2_sel  ,
  // Pipeline outputs
  output logic        ex_d_valid          ,
  output logic        ex_d_is_rd_write    ,
  output logic [ 4:0] ex_d_rd_addr        ,
  output logic        ex_d_is_csr_write   ,
  output logic        ex_d_is_csr_read    ,
  output logic [11:0] ex_d_csr_addr       ,
  output logic [31:0] ex_d_csr_wdata      ,
  output logic [31:0] ex_d_store_wdata    ,
  output logic [31:0] ex_d_alu_csr_result ,
  output logic        ex_d_is_mem_read    ,
  output logic        ex_d_is_mem_write   ,
  output logic        ex_d_is_memsize_h   ,
  output logic        ex_d_is_memsize_hu  ,
  output logic        ex_d_is_memsize_b   ,
  output logic        ex_d_is_memsize_bu  ,
  output logic        ex_d_is_memsize_w   ,
  output logic        ex_d_is_branch      ,
  output logic        ex_d_is_jump        ,
  output logic        ex_d_is_jal         ,
  output logic        ex_d_is_jalr        ,
  output logic        ex_d_branch_predict ,
  output logic [ 5:0] ex_d_pht_idx        ,
  output logic [31:0] ex_d_pc             ,
  output logic [31:0] ex_d_pc_plus_4      ,
  output logic [31:0] ex_d_jaddr          ,
  output logic        ex_d_jump_taken     ,
  output logic        ex_d_trap_valid     ,
  output logic [31:0] ex_d_trap_pc        ,
  output logic [31:0] ex_d_trap_mcause
`ifdef RISCV_FORMAL
  ,
  // RVFI outputs
  output logic [31:0] ex_d_next_pc        ,
  output logic [31:0] ex_d_insn           ,
  output logic        ex_d_intr           ,
  output logic [ 4:0] ex_d_rs1_addr       ,
  output logic [ 4:0] ex_d_rs2_addr       ,
  output logic [31:0] ex_d_rs1_rdata      ,
  output logic [31:0] ex_d_rs2_rdata      ,
  output logic [31:0] ex_d_csr_rdata      ,
  output logic [31:0] ex_d_trap_insn      ,
  output logic [31:0] ex_d_trap_next_pc   ,
  output logic [ 4:0] ex_d_trap_rs1_addr  ,
  output logic [ 4:0] ex_d_trap_rs2_addr  ,
  output logic [ 4:0] ex_d_trap_rd_addr   ,
  output logic [31:0] ex_d_trap_rs1_rdata ,
  output logic [31:0] ex_d_trap_rs2_rdata ,
  output logic [31:0] ex_d_trap_rd_wdata
`endif
);
  logic [31:0] ex_rs1_rdata  ;
  logic [31:0] ex_src_a      ;
  logic [31:0] ex_rs2_rdata  ;
  logic [31:0] ex_src_b      ;
  logic [31:0] ex_pc_base    ;
  logic [31:0] ex_csr_bitmask;
  logic [31:0] ex_csr_wdata  ;
  logic        ex_branch_cond;
  logic [31:0] ex_jaddr      ;
  logic [31:0] ex_alu_result ;
  logic ex_jump_taken;
  logic ex_misaligned_jump;

  // select rs1 read data
  always_comb begin
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
  always_comb begin
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
  always_comb begin
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
  always_comb begin
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
  always_comb begin
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
  always_comb begin
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
  always_comb begin
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

  always_comb
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
  always_comb begin
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
  always_comb begin
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

  logic [31:0] ex_next_pc;
  assign ex_next_pc = (ex_jump_taken) ? ex_jaddr : ex_q_pc_plus_4;
  always_comb
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
endmodule
