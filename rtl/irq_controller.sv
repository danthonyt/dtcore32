module irq_controller (
    input  logic        clk_i,
    input  logic        rst_i,
    input  logic [31:0] irq_sources_i,
    output logic        cpu_irq_pending_o,
    output logic [ 4:0] active_irq_o
);
  // OR all sources for CPU pending
  assign cpu_irq_pending_o = |irq_sources_i;

  // Priority encoder: lowest numbered IRQ has highest priority
  logic [4:0] highest_irq;
  integer i;
  always_comb begin
    highest_irq = 5'd0;  // default if none active
    for (i = 0; i < 32; i = i + 1) begin
      if (irq_sources_i[i] && highest_irq == 5'd0) begin
        highest_irq = i[4:0];
      end
    end
  end
  assign active_irq_o = highest_irq;
endmodule
