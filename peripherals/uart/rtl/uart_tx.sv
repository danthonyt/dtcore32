// CLKS_PER_BIT = (frequency of clk)/(frequency of uart)
// Example: 10 MHz Clock, 115200 baud uart
// (10,000,000)/(115,200) = 87
module uart_tx #(
    // 5 to 9 data bits
    parameter DATA_WIDTH   = 8,
    // baud rate
    parameter CLKS_PER_BIT = 87
) (
    input logic CLK,
    input logic RSTN,
    input logic START,
    input logic [DATA_WIDTH-1:0] din,
    output logic SERIAL_TX,
    output logic DONE,
);
  // FSM states
  enum int unsigned {
    IDLE_TX,
    START_TX,
    DATA_TX,
    STOP_TX
  } state;
  // index of TX DATA
  int unsigned index;
  // clock cycle count 
  int unsigned cnt_clock;

  always_ff @(posedge CLK) begin
    if (!RSTN) begin
      state <= IDLE_TX;
    end else begin
      case (state)
        IDLE_TX: begin
          //output
          SERIAL_TX <= 1'b1;
          index <= 0;
          cnt_clock <= 0;
          DONE <= 0;
          //next state
          if (START) state <= START_TX;
          else state <= IDLE_TX;
        end
        START_TX: begin
          //output
          SERIAL_TX <= 1'b0;
          index <= 0;
          cnt_clock <= cnt_clock + 1;
          DONE <= 0;
          //next state
          if (cnt_clock < CLKS_PER_BIT - 1) state <= START_TX;
          else begin
            cnt_clock <= 0;
            state <= DATA_TX;
          end
        end
        DATA_TX: begin
          //output
          SERIAL_TX <= din[index];
          DONE <= 0;
          //next state
          if (cnt_clock < (CLKS_PER_BIT - 1)) begin
            cnt_clock <= cnt_clock + 1;
          end else begin
            cnt_clock <= 0;
            if (index < (DATA_WIDTH - 1)) begin
              index <= index + 1;
            end else begin
              index <= 0;
              state <= STOP_TX;
            end
          end
        end
        STOP_TX: begin
          //output
          SERIAL_TX <= 1'b1;
          index <= 0;
          cnt_clock <= cnt_clock + 1;
          DONE <= 0;
          //next state
          if (cnt_clock < CLKS_PER_BIT - 1) state <= STOP_TX;
          else begin
            state <= IDLE_TX;
            DONE  <= 1'b1;
          end
        end
        default: begin
          SERIAL_TX <= 1'b1;
          index <= 0;
          cnt_clock <= 0;
          DONE <= 0;
          state <= IDLE_TX;
        end
      endcase
    end
  end

endmodule

