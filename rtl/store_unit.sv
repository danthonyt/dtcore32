module store_unit
  import params_pkg::*;
(
    input mem_op_t mem_op_i,
    input logic [1:0] waddr_lower2_i,
    input logic [31:0] wdata_unformatted_i,
    output logic misaligned_store_o,
    output logic [3:0] wstrb_o,
    output logic [31:0] wdata_o
);

  logic misaligned_store;
  logic [3:0] wstrb;
  logic [31:0] store_wdata_formatted;
  always_comb begin
    misaligned_store = 0;
    store_wdata_formatted = 0;
    wstrb = 0;
    case (mem_op_i)
      MEM_SW: begin
        wstrb = 4'hf;
        store_wdata_formatted = wdata_unformatted_i;
      end
      MEM_SH: begin
        wstrb = 4'h3 << waddr_lower2_i[1] * 2;
        store_wdata_formatted = wdata_unformatted_i << waddr_lower2_i[1] * 16;
      end
      MEM_SB: begin
        wstrb = 4'b1 << waddr_lower2_i;
        store_wdata_formatted = wdata_unformatted_i << waddr_lower2_i * 8;
      end
      default:;
    endcase
  end

  assign wstrb_o = misaligned_store ? 0 : wstrb;
  assign misaligned_store_o = 0;
  assign wdata_o = misaligned_store ? 0 : store_wdata_formatted;

endmodule
