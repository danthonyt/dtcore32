`timescale 1ns/1ps
module testbench();
    localparam DATA_WIDTH = 8;
    localparam CLKS_PER_BIT= 87;
    logic [9:0] test = { 1'b1,8'b1010_1010,1'b0};
    logic clk;
    logic reset;
    logic start;
    logic serial_rx;
    logic [(DATA_WIDTH-1):0] din_tx;
    logic [(DATA_WIDTH-1):0] dout_rx;
    logic serial_tx;
    logic done;
    uart_top #(
        // 5 to 9 data bits
        .DATA_WIDTH(DATA_WIDTH),
        // baud rate
        .CLKS_PER_BIT(CLKS_PER_BIT)
    )
    tb (
        .clk(clk),
        .reset(reset),
        .start(start),
        .serial_rx(serial_rx),
        .din_tx(din_tx),
        .dout_rx(dout_rx),
        .serial_tx(serial_tx),
        .done(done)
    );
    initial begin
        clk = 0;
        forever begin
            #5 clk = !clk;
        end
    end

    initial begin
        reset <= 1;
        serial_rx <= 1;
        start <= 0;
        din_tx <= 8'b1010_1010;
        @(negedge clk);
        reset <= 0; 
        @(negedge clk);
        for (int i = 0; i<=9 ;i++ ) begin
            serial_rx <= test[i];
            repeat(CLKS_PER_BIT)
                @(negedge clk);
        end
        assert (dout_rx == test[8:1]) $display("PASS");
        else   $error("RECEIVE FAIL");
        // test transmit
        start <= 1;
        // go to middle of start bit
        @(negedge clk);
        start <= 0;
        repeat(CLKS_PER_BIT/2)
            @(negedge clk);
        assert (serial_tx == 0) 
        else   $error("START BIT NOT ASSERTED");
        for (int i = 0; i<= 7;i++ ) begin
            repeat(CLKS_PER_BIT)
                @(negedge clk);
            assert (serial_tx == din_tx[i])
                else $error("DATA MISMATCH");
        end
        repeat(CLKS_PER_BIT)
                @(negedge clk);
        assert (serial_tx == 1) 
        else   $error("STOP BIT NOT RECEIVED");
        $display("TEST PASSED");
        $finish;

    end

endmodule