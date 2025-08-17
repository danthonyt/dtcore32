module dtcore32_top_tb;
  logic clk = 0;
  logic rst;
  logic rx;
  logic tx;

  always #5 clk = ~clk;

  dtcore32_top dtcore32_top_inst (
      .CLK(clk),
      .RST(rst),
      .RX (rx),
      .TX (tx)
  );

  initial begin
    rst = 1;
    #20 rst = 0;

    // optional: run simulation for some cycles
    #1000 $finish;
  end

endmodule
