//===========================================================
// Project    : RISC-V CPU / Digital Logic Utilities
// File       : pulse_generator.sv
// Module     : pulse_generator
// Description: Generates a single-cycle pulse when the enable
//              input (`en_i`) transitions high. Useful for 
//              triggering events in a synchronous design.
//
// Inputs:
//   clk_i   - System clock
//   rst_i   - Synchronous reset
//   en_i    - Enable signal; pulse generated on rising edge
//
// Outputs:
//   pulse_o - Single-cycle output pulse
//
// Notes:
//   - Works combinationally with internal state to detect rising edges.
//   - Can be used for triggering pipeline events, counters, or other
//     modules that require a single-cycle enable.
//   - Fully synchronous design; pulse width is exactly one clock cycle.
//
// Author     : David Torres
// Date       : 2025-09-16
//===========================================================
`include "formal_defs.svh"
module pulse_generator(
    input  logic clk_i,
    input  logic rst_i,
    input  logic en_i,
    output logic pulse_o
);
    logic en_q;

    always_ff @(posedge clk_i) begin
        if (rst_i) begin
            en_q <= 0;
        end else begin
            en_q <= en_i;
        end
    end

    always_ff @(posedge clk_i) begin
        if (rst_i) begin
            pulse_o <= 0; 
        // generate pulse on rising edge of en_i
        end else if (!en_q && en_i) begin
            pulse_o <= 1;
        end else begin
            pulse_o <= 0;
        end
    end

   /******************************/
   // FORMAL
   //*****************************/
   `ifdef RISCV_FORMAL 
   logic pulse_prev;
   logic en_prev;
   initial begin
    pulse_prev = 0;
    en_prev = 0;
   end
    always_ff@(posedge clk_i)begin
        // output pulse should never be held for longer than one cycle
        if (pulse_o) assert(!pulse_prev);
        pulse_prev <= pulse_o;
        // output pulse should be low if enable is low
        if (!en_prev) assert (!pulse_o);
        en_prev <= en_i;
    end
   `endif

endmodule
