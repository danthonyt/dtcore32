// CLKS_PER_BIT = (frequency of clk)/(frequency of uart)
// Example: 10 MHz Clock, 115200 baud uart
// (10,000,000)/(115,200) = 87
module uart_rx #(
    // 5 to 9 data bits 
    parameter DATA_WIDTH   = 8,
    // baud rate
    parameter CLKS_PER_BIT = 87
) (
    input logic CLK,
    input logic RSTN,
    input logic SERIAL_RX,
    output logic [DATA_WIDTH-1:0] DOUT
);
  typedef enum {
    RESET_RX,
    IDLE_RX,
    START_RX,
    DATA_RX,
    STOP_RX
  } fsm_state;
  fsm_state state;
  fsm_state next_state;
  // index of TX DATA
  int unsigned index;
  // clock cycle count 
  int unsigned cycle_cnt;
  logic [DATA_WIDTH-1:0] shift_reg;
  logic index_cntr_en;
  logic cycle_cntr_en;
  logic shift_en;
  
  always_comb begin
    index_cntr_en = 0;
    cycle_cntr_en = 0;
    shift_en = 0;
    next_state = state;
    case (state)
      RESET_RX: begin
        next_state = IDLE_RX;
      end
      IDLE_RX: begin
        if (SERIAL_RX == 1'b0) next_state = START_RX;
      end
      START_RX: begin
        cycle_cntr_en = 1;
        if (SERIAL_RX == 1'b1) begin
          next_state = IDLE_RX;
        end else if (cycle_cnt >= (((CLKS_PER_BIT - 1) / 2) - 1)) begin
          next_state = DATA_RX;
          cycle_cntr_en = 0;
        end
      end
      DATA_RX: begin
        cycle_cntr_en = 1;
        index_cntr_en = 1;
        if (cycle_cnt >= (CLKS_PER_BIT - 1)) begin
          shift_en = 1;
          if (index >= (DATA_WIDTH - 1)) begin
            cycle_cntr_en = 0;
            next_state = STOP_RX;
          end
        end
      end
      STOP_RX: begin
        cycle_cntr_en = 1;
        if (cycle_cnt >= (CLKS_PER_BIT - 1)) next_state = IDLE_RX;
      end
      default: begin
        next_state = IDLE_RX;
      end
    endcase
  end
  always_ff @(posedge CLK) begin
    if (!RSTN) begin
      state <= RESET_RX;
    end else begin
      state <= next_state;
    end
  end

  // index counter
  // incerements every time cycle cnt reaches its max count value
  always_ff @(posedge CLK) begin
    if (!RSTN || !index_cntr_en) begin
      index <= 0;
    end else begin
      if (cycle_cnt >= (CLKS_PER_BIT - 1)) index <= index + 1;
    end
  end

  // clock cycle counter
  // increments every time it reaches the number of clk cycles per bit,
  // which is selected based on the desired baud rate and source clock frequency
  always_ff @(posedge CLK) begin
    if (!RSTN || !cycle_cntr_en) begin
      cycle_cnt <= 0;
    end else begin
      if (cycle_cnt >= (CLKS_PER_BIT - 1)) cycle_cnt <= 0;
      else cycle_cnt <= cycle_cnt + 1;
    end
  end

  // shift register for dout
  // shifts the register by one bit for every clock it is enabled,
  // shifting in the serial rx input.
  always_ff @(posedge CLK) begin
    if (!RSTN) begin
      shift_reg <= 0;
    end else if (shift_en) begin
      shift_reg <= {SERIAL_RX, shift_reg[7:1]};
    end
  end

  assign DOUT = shift_reg;

  /******************************************/
  //
  //    FORMAL VERIFICATION
  //
  /******************************************/
`ifdef FORMAL
  initial assume (RSTN == 0);
  int f_cycle_count;
  initial f_cycle_count = 0;
  always_ff @(posedge CLK) begin
    f_cycle_count <= f_cycle_count + 1;
    if (f_cycle_count >= 1) assume property (@(posedge CLK) disable iff (!RSTN) ($stable(SERIAL_RX)));
    if (f_cycle_count >= 3) f_cycle_count <= 0;
  end
  // the serial input should hold stable for the expected baud rate
  // assume baud rate requires 4 clocks per bit
  successful_receive:
  cover property (@(posedge CLK) disable iff (!RSTN) 
  (DOUT == 8'hda ));
  idle_back_to_idle:
  cover property (@(posedge CLK) disable iff (!RSTN) 
  (state == IDLE_RX) ##[1:$] (state == START_RX)  ##[1:$] (state == DATA_RX) ##[1:$] (state == STOP_RX) ##[1:$] (state == IDLE_RX));
`endif
endmodule
