module riscv_formal_if (
  // --------------------
  // Clock / reset
  // --------------------
  input  logic        clk_i,
  input  logic        rst_i,

  input logic mem_wb_stall,
  input logic [31:0] trap_handler_addr,
  input logic [31:0] wb_csr_wmask,
  input logic [31:0] wb_csr_rmask,
  
  // --------------------
  // Pipeline commit signals (WB stage)
  // --------------------
  input  logic [31:0] wb_q_pc,
  input  logic [31:0] wb_q_next_pc,
  input  logic [31:0] wb_q_insn,
  input  logic        wb_q_valid,
  input  logic        wb_q_trap_valid,
  input  logic        wb_q_intr,

  // Register file commit
  input  logic [4:0]  wb_q_rs1_addr,
  input  logic [4:0]  wb_q_rs2_addr,
  input  logic [31:0] wb_q_rs1_rdata,
  input  logic [31:0] wb_q_rs2_rdata,
  input  logic        wb_q_is_rd_write,
  input  logic [4:0]  wb_rd_addr,
  input  logic [31:0] wb_rd_wdata,

  // CSR commit
  input  logic [11:0] wb_csr_addr,
  input  logic [31:0] wb_q_csr_rdata,
  input  logic [31:0] wb_q_csr_wdata,
  input  logic        wb_q_is_csr_read,
  input  logic        wb_q_is_csr_write,

  // Memory commit
  input  logic [31:0] wb_q_mem_addr,
  input  logic [31:0] wb_q_load_rdata,
  input  logic [31:0] wb_q_store_wdata,
  input  logic [3:0] wb_q_load_rmask,
  input  logic [3:0] wb_q_store_wmask,

  // Trap commit
  input  logic [31:0] wb_q_trap_insn,
  input  logic [31:0] wb_q_trap_pc,
  input  logic [31:0] wb_q_trap_next_pc,
  input  logic [4:0]  wb_q_trap_rs1_addr,
  input  logic [4:0]  wb_q_trap_rs2_addr,
  input  logic [4:0]  wb_q_trap_rd_addr,
  input  logic [31:0] wb_q_trap_rs1_rdata,
  input  logic [31:0] wb_q_trap_rs2_rdata,
  input  logic [31:0] wb_q_trap_rd_wdata, // optional if needed

  // --------------------
  // Outputs to RVFI
  // --------------------
  output logic        rvfi_valid,
  output logic [63:0] rvfi_order,
  output logic [31:0] rvfi_insn,
  output logic        rvfi_trap,
  output logic        rvfi_halt,
  output logic        rvfi_intr,
  output logic [1:0]  rvfi_mode,
  output logic [1:0]  rvfi_ixl,

  output logic [4:0]  rvfi_rs1_addr,
  output logic [4:0]  rvfi_rs2_addr,
  output logic [31:0] rvfi_rs1_rdata,
  output logic [31:0] rvfi_rs2_rdata,

  output logic [4:0]  rvfi_rd_addr,
  output logic [31:0] rvfi_rd_wdata,

  output logic [31:0] rvfi_pc_rdata,
  output logic [31:0] rvfi_pc_wdata,

  output logic [31:0] rvfi_mem_addr,
  output logic [31:0] rvfi_mem_rdata,
  output logic [31:0] rvfi_mem_wdata,
  output logic [3:0] rvfi_mem_rmask,
  output logic [3:0] rvfi_mem_wmask,

  // CSR RVFI outputs
  output logic [63:0] rvfi_csr_mcycle_rdata,
  output logic [63:0] rvfi_csr_mcycle_wdata,
  output logic [63:0] rvfi_csr_mcycle_rmask,
  output logic [63:0] rvfi_csr_mcycle_wmask,

  output logic [63:0] rvfi_csr_minstret_rdata,
  output logic [63:0] rvfi_csr_minstret_wdata,
  output logic [63:0] rvfi_csr_minstret_rmask,
  output logic [63:0] rvfi_csr_minstret_wmask,

  output logic [31:0] rvfi_csr_mcause_rdata,
  output logic [31:0] rvfi_csr_mcause_wdata,
  output logic [31:0] rvfi_csr_mcause_rmask,
  output logic [31:0] rvfi_csr_mcause_wmask,

  output logic [31:0] rvfi_csr_mtvec_rdata,
  output logic [31:0] rvfi_csr_mtvec_wdata,
  output logic [31:0] rvfi_csr_mtvec_rmask,
  output logic [31:0] rvfi_csr_mtvec_wmask,

  output logic [31:0] rvfi_csr_mepc_rdata,
  output logic [31:0] rvfi_csr_mepc_wdata,
  output logic [31:0] rvfi_csr_mepc_rmask,
  output logic [31:0] rvfi_csr_mepc_wmask
);

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

  always_comb
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

  always_comb
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
          ; // unimplemented address
      endcase
    end

  always_ff @(posedge clk_i)
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
endmodule
