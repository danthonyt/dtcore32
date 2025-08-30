module soc_tb ();
  logic clk = 0;
  logic rst;
  logic rx;
  logic tx;

  always #5 clk = ~clk;

  soc_top soc_top_inst (
      .CLK_I(clk),
      .RST_I(rst),
      .RX_I (rx),
      .TX_O (tx)
  );
  localparam IMEM_BASE_ADDR = 0;
  localparam IMEM_LENGTH = 1024;
  localparam DMEM_BASE_ADDR = 32'h0010_0000;
  localparam DMEM_LENGTH = 1024;
  localparam UART_BASE_ADDR = 32'h0100_0000;
  localparam UART_LENGTH = 16;
  logic [31:0] mem_addr;
  assign mem_addr = soc_top_inst.CPU_MEM_CMD_ADDR_I;

  always @(posedge clk) begin
    if (soc_top_inst.dtcore32_inst.mem_cmd_req) begin
      if (mem_addr >= IMEM_BASE_ADDR && mem_addr < IMEM_BASE_ADDR + IMEM_LENGTH) begin
        $error("MEM stage tried to read IMEM");
        $display("MEM stage PC: %h", soc_top_inst.dtcore32_inst.mem_pipeline.pc);
        $finish();
      end else if (mem_addr >= DMEM_BASE_ADDR && mem_addr < DMEM_BASE_ADDR + DMEM_LENGTH) begin
        $display("MEM stage tried to read DMEM");
      end else if (mem_addr >= UART_BASE_ADDR && mem_addr < UART_BASE_ADDR + UART_LENGTH) begin
        $display("MEM stage tried to read UART");
       
      end else begin
        $error("MEM stage tried to read unknown peripheral");
        $finish();
      end
    end
  end

  initial begin
    rst = 1;
    #20 rst = 0;

    // optional: run simulation for some cycles
    #4us $finish;
  end
endmodule
