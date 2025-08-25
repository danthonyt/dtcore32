module store_unit
  import params_pkg::*;
#(
    BUS_WIDTH = 32
) (
    input mem_op_t MEM_OP,
    input logic [1:0] ADDR_LSB2,
    output logic STORE_TRAP_VALID,
    output logic [30:0] STORE_TRAP_MCAUSE,
    output logic [(BUS_WIDTH/8)-1:0] WSTRB,
    output logic [3:0] STORE_WMASK
);

  logic misaligned_store;
  logic [3:0] wmask;
  always_comb begin
    misaligned_store = 0;
    wmask = 4'h0;
    WSTRB = 0;
    case (MEM_OP)
      MEM_SW: begin
        wmask = 4'hf;
        WSTRB = 4'hf;
      end
      MEM_SH: begin
        wmask = 4'h3;
        WSTRB = 4'h3 << ADDR_LSB2;
      end
      MEM_SB: begin
        wmask = 4'b1;
        WSTRB = 4'b1 << ADDR_LSB2;
      end
    endcase
  end

  assign STORE_WMASK = misaligned_store ? 0 : wmask;
  assign STORE_TRAP_MCAUSE = misaligned_store ? TRAP_CODE_STORE_ADDR_MISALIGNED : 0;
  assign STORE_TRAP_VALID = misaligned_store;

endmodule
