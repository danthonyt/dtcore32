module mem_stage
  import params_pkg::*;
(
    input logic clk_i,
    input logic rst_i,
    input ex_mem_t mem_pipeline_q,
    output mem_wb_t mem_pipeline_d,
    // memory request
    input logic [31:0] mem_rdata_i,
    input logic mem_done_i,
    output logic mem_valid_o,
    output logic mem_wen_o,
    output logic [31:0] mem_addr_o,
    output logic [31:0] mem_wdata_o,
    output logic [3:0] mem_strb_o

);
  logic [3:0] mem_load_rmask_comb;
  logic [31:0] mem_load_rdata_d;
  logic [31:0] mem_store_wdata_d;
  logic [30:0] mem_store_trap_mcause;
  logic mem_store_trap_valid;
  logic [30:0] mem_load_trap_mcause;
  logic mem_load_trap_valid;
  logic [3:0] mem_store_wmask_d;
  logic [3:0] mem_load_rmask_d;
  logic [3:0] mem_store_wmask_comb;
  logic mem_req;
  logic [31:0] mem_store_wdata_formatted;
  logic [31:0] mem_load_rdata_raw;
  logic [31:0] mem_load_rdata_formatted;

  // start a wishbone req if a memory instruction and no trap
  assign mem_req = !mem_pipeline_q.trap_valid && (mem_pipeline_q.mem_op != MEM_NONE);

  assign mem_wen_o = mem_pipeline_q.mem_op[4] & mem_pipeline_q.mem_op[3];
  assign mem_addr_o = mem_pipeline_q.alu_csr_result;

  assign mem_store_wdata_d = mem_store_wdata_formatted;
  assign mem_store_wmask_d =  (mem_pipeline_q.mem_op[4] & mem_pipeline_q.mem_op[3]) ? mem_store_wmask_comb : 0;

  assign mem_load_rdata_d = mem_load_rdata_formatted;
  assign mem_load_rmask_d = (mem_pipeline_q.mem_op[4] & !mem_pipeline_q.mem_op[3]) ? mem_load_rmask_comb : 0;

  assign mem_load_rdata_raw = mem_rdata_i;
  assign mem_strb_o = mem_store_wmask_d;
  assign mem_wdata_o = mem_store_wdata_formatted;

  // a memory request sends a start pulse
  pulse_generator pulse_generator_inst (
      .clk_i(clk_i),
      .rst_i(rst_i),
      .en_i(mem_req && !mem_done_i),
      .pulse_o(mem_valid_o)
  );

  store_unit store_unit_inst (
      .MEM_OP(mem_pipeline_q.mem_op),
      .ADDR_LSB2(mem_pipeline_q.alu_csr_result[1:0]),
      .STORE_WDATA_RAW(mem_pipeline_q.store_wdata),
      .STORE_TRAP_VALID(mem_store_trap_valid),
      .STORE_TRAP_MCAUSE(mem_store_trap_mcause),
      .WMASK(mem_store_wmask_comb),
      .STORE_WDATA_FORMATTED(mem_store_wdata_formatted)
  );

  load_unit load_unit_inst (
      .MEM_OP(mem_pipeline_q.mem_op),
      .ADDR_LSB2(mem_pipeline_q.alu_csr_result[1:0]),
      .RDATA_RAW(mem_load_rdata_raw),
      .LOAD_TRAP_VALID(mem_load_trap_valid),
      .LOAD_TRAP_MCAUSE(mem_load_trap_mcause),
      .LOAD_RMASK(mem_load_rmask_comb),
      .LOAD_FORMATTED(mem_load_rdata_formatted)
  );

  always_comb begin
    mem_pipeline_d.valid          = mem_pipeline_q.valid;
    mem_pipeline_d.pc_plus_4      = mem_pipeline_q.pc_plus_4;
    mem_pipeline_d.rd_addr        = mem_pipeline_q.rd_addr;
    mem_pipeline_d.csr_addr       = mem_pipeline_q.csr_addr;
    mem_pipeline_d.csr_wdata      = mem_pipeline_q.csr_wdata;
    mem_pipeline_d.csr_rdata      = mem_pipeline_q.csr_rdata;
    mem_pipeline_d.result_sel     = mem_pipeline_q.result_sel;
    mem_pipeline_d.load_rdata     = mem_load_rdata_d;
    mem_pipeline_d.alu_csr_result = mem_pipeline_q.alu_csr_result;
  end

  // generate a trap on misaligned store or load
  always_comb begin
    mem_pipeline_d.trap_valid  = 0;
    mem_pipeline_d.trap_mcause = 'x;
    mem_pipeline_d.trap_pc = mem_pipeline_q.pc;
    if (mem_pipeline_q.trap_valid) begin
      mem_pipeline_d.trap_valid  = 1;
      mem_pipeline_d.trap_mcause = mem_pipeline_q.trap_mcause;
    end else if (mem_store_trap_valid) begin
      mem_pipeline_d.trap_valid  = 1;
      mem_pipeline_d.trap_mcause = {1'b0, mem_store_trap_mcause};
    end else if (mem_load_trap_valid) begin
      mem_pipeline_d.trap_valid  = 1;
      mem_pipeline_d.trap_mcause = {1'b0, mem_load_trap_mcause};
    end
  end


`ifdef RISCV_FORMAL
  trap_info_t mem_trap_d;
  always_comb begin
    mem_trap_d.insn = mem_pipeline_q.insn;
    mem_trap_d.pc = mem_pipeline_q.pc;
    mem_trap_d.next_pc = mem_pipeline_q.next_pc;
    mem_trap_d.rs1_addr = mem_pipeline_q.rs1_addr;
    mem_trap_d.rs2_addr = mem_pipeline_q.rs2_addr;
    mem_trap_d.rd_addr = mem_pipeline_q.rd_addr;
    mem_trap_d.rs1_rdata = mem_rs1_rdata_d;
    mem_trap_d.rs2_rdata = mem_rs2_rdata_d;
    mem_trap_d.rd_wdata = 0;
    if (mem_pipeline_q.trap_valid) begin
      mem_trap_d = mem_pipeline_q.rvfi_trap_info;
    end
  end

  always_comb begin
    mem_pipeline_d.pc             = mem_pipeline_q.pc;
    mem_pipeline_d.next_pc        = mem_pipeline_q.next_pc;
    mem_pipeline_d.insn           = mem_pipeline_q.insn;
    mem_pipeline_d.intr           = mem_pipeline_q.intr;
    mem_pipeline_d.rs1_addr       = mem_pipeline_q.rs1_addr;
    mem_pipeline_d.rs2_addr       = mem_pipeline_q.rs2_addr;
    mem_pipeline_d.rs1_rdata      = mem_pipeline_q.rs1_rdata;
    mem_pipeline_d.rs2_rdata      = mem_pipeline_q.rs2_rdata;
    mem_pipeline_d.load_rmask     = mem_load_rmask_d;
    mem_pipeline_d.store_wmask    = mem_store_wmask_d;
    mem_pipeline_d.store_wdata    = mem_store_wdata_d;
    mem_pipeline_d.rvfi_trap_info = mem_trap_d;
  end
`endif
endmodule
