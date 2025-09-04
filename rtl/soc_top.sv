module soc_top (
    input  logic clk_i,
    input  logic rst_i,
    input  logic rx_i,
    output logic tx_o

);
  localparam MEM_DEPTH = 2560;
  localparam CLKS_PER_BIT = 860;
  localparam WISHBONE_ADDR_WIDTH = 32;
  localparam WISHBONE_BUS_WIDTH = 32;

  logic [31:0] imem_rdata;
  logic [31:0] imem_addr;
  logic [31:0] mem_rdata;
  logic mem_done;
  logic mem_valid;
  logic mem_wen;
  logic [31:0] mem_addr;
  logic [31:0] mem_wdata;
  logic [3:0] mem_strb;

  logic [31:0] cpu_wbm_dat_i;
  logic cpu_wbm_err;
  logic cpu_wbm_ack;
  logic cpu_wbm_cyc;
  logic cpu_wbm_stb;
  logic [31:0] cpu_wbm_adr;
  logic cpu_wbm_we;
  logic [31:0] cpu_wbm_dat_o;
  logic [3:0] cpu_wbm_sel;
  logic [31:0] dmem_rdata;
  logic [31:0] dmem_addr;
  logic dmem_en;
  logic dmem_wen;
  logic [31:0] dmem_wdata;
  logic [3:0] dmem_wstrb;

  logic [WISHBONE_ADDR_WIDTH-1:0] ic_wbs_adr;
  logic ic_wbs_we;
  logic [WISHBONE_BUS_WIDTH-1:0] ic_wbs_dat_i;
  logic [WISHBONE_BUS_WIDTH/8-1:0] ic_wbs_sel;
  logic uart_wbs_cyc;
  logic uart_wbs_stb;
  logic [WISHBONE_BUS_WIDTH-1:0] uart_wbs_dat_o;
  logic uart_wbs_ack;
  logic uart_wbs_err;

  dtcore32 dtcore32_inst (
      .clk_i(clk_i),
      .rst_i(rst_i),
      .imem_rdata_i(imem_rdata),
      .imem_addr_o(imem_addr),
      .mem_rdata_i(mem_rdata),
      .mem_done_i(mem_done),
      .mem_valid_o(mem_valid),
      .mem_wen_o(mem_wen),
      .mem_addr_o(mem_addr),
      .mem_wdata_o(mem_wdata),
      .mem_strb_o(mem_strb)
  );

  cpu_bus_master cpu_bus_master_inst (
      .clk_i(clk_i),
      .rst_i(rst_i),
      .mem_valid_i(mem_valid),
      .mem_wen_i(mem_wen),
      .mem_addr_i(mem_addr),
      .mem_wdata_i(mem_wdata),
      .mem_strb_i(mem_strb),
      .mem_rdata_o(mem_rdata),
      .mem_done_o(mem_done),
      .cpu_wbm_dat_i(cpu_wbm_dat_i),
      .cpu_wbm_err_i(cpu_wbm_err),
      .cpu_wbm_ack_i(cpu_wbm_ack),
      .cpu_wbm_cyc_o(cpu_wbm_cyc),
      .cpu_wbm_stb_o(cpu_wbm_stb),
      .cpu_wbm_adr_o(cpu_wbm_adr),
      .cpu_wbm_we_o(cpu_wbm_we),
      .cpu_wbm_dat_o(cpu_wbm_dat_o),
      .cpu_wbm_sel_o(cpu_wbm_sel),
      .dmem_rdata_i(dmem_rdata),
      .dmem_addr_o(dmem_addr),
      .dmem_en_o(dmem_en),
      .dmem_wen_o(dmem_wen),
      .dmem_wdata_o(dmem_wdata),
      .dmem_wstrb_o(dmem_wstrb)
  );

  ram #(
      .MEM_DEPTH(MEM_DEPTH)
  ) dmem_inst (
      .clk_i(clk_i),
      .addr_i(dmem_addr[$clog2(MEM_DEPTH)-1+2:2]),
      .en_i(dmem_en),
      .wen_i(dmem_wen),
      .wdata_i(dmem_wdata),
      .wstrb_i(dmem_wstrb),
      .rdata_o(dmem_rdata)
  );

  rom #(
      .MEM_DEPTH(MEM_DEPTH)
  ) imem_inst (
      .clk_i  (clk_i),
      .addr_i (imem_addr[$clog2(MEM_DEPTH)-1+2:2]),
      .rdata_o(imem_rdata)
  );

  uart_wb_wrapper #(
      .CLKS_PER_BIT(CLKS_PER_BIT)
  ) uart_wb_wrapper_inst (
      .clk_i(clk_i),
      .rst_i(rst_i),
      .wbs_adr_i(ic_wbs_adr[3:0]),
      .wbs_we_i(ic_wbs_we),
      .wbs_dat_i(ic_wbs_dat_i),
      .wbs_cyc_i(uart_wbs_cyc),
      .wbs_stb_i(uart_wbs_stb),
      .wbs_dat_o(uart_wbs_dat_o),
      .wbs_ack_o(uart_wbs_ack),
      .wbs_err_o(uart_wbs_err),
      .rx_i(rx_i),
      .tx_o(tx_o)
  );

  wb_interconnect #(
      .WISHBONE_ADDR_WIDTH(WISHBONE_ADDR_WIDTH),
      .WISHBONE_BUS_WIDTH (WISHBONE_BUS_WIDTH)
  ) wb_interconnect_inst (
      .wbm_cyc(cpu_wbm_cyc),
      .wbm_stb(cpu_wbm_stb),
      .wbm_adr(cpu_wbm_adr),
      .wbm_we(cpu_wbm_we),
      .wbm_dat_o(cpu_wbm_dat_o),
      .wbm_sel(cpu_wbm_sel),
      .wbm_dat_i(cpu_wbm_dat_i),
      .wbm_err(cpu_wbm_err),
      .wbm_ack(cpu_wbm_ack),
      .ic_wbs_adr(ic_wbs_adr),
      .ic_wbs_we(ic_wbs_we),
      .ic_wbs_dat_i(ic_wbs_dat_i),
      .ic_wbs_sel(ic_wbs_sel),
      .uart_wbs_cyc(uart_wbs_cyc),
      .uart_wbs_stb(uart_wbs_stb),
      .uart_wbs_dat_o(uart_wbs_dat_o),
      .uart_wbs_ack(uart_wbs_ack),
      .uart_wbs_err(uart_wbs_err)
  );
endmodule
