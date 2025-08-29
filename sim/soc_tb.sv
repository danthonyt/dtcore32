module soc_tb();
  logic clk = 0;
  logic rst;
  logic rx;
  logic tx;

  always #5 clk = ~clk;

  soc_top  soc_top_inst (
    .CLK_I(clk),
    .RST_I(rst),
    .RX_I(rx),
    .TX_O(tx)
  );

  initial begin
    rst = 1;
    #20 rst = 0;

    // optional: run simulation for some cycles
    #4us $finish;
  end
endmodule
