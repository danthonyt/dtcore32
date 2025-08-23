module store_unit
  import params_pkg::*;
(
    input logic [4:0] MEM_OP,
    input logic [1:0] ADDR_LSB2,
    output logic STORE_TRAP_VALID,
    output logic [30:0] STORE_TRAP_MCAUSE,
    output logic [3:0] AXIL_WSTRB,
    output logic [3:0] STORE_WMASK
);

  logic misaligned_store;
  logic [3:0] wmask;
  always_comb begin
    misaligned_store = 0;
    wdata_formatted = 0;
    wmask = 4'h0;
    AXIL_WSTRB = 0;
    case (MEM_OP)
      MEM_SW: begin
        wmask = 4'hf;
        AXIL_WSTRB = 4'hf;
      end
      MEM_SH: begin
        wmask = 4'h3;
        AXIL_WSTRB = 4'h3 << ADDR_LSB2;
      end
      MEM_SB: begin
        wmask = 4'b1;
        AXIL_WSTRB = 4'b1 << ADDR_LSB2;
      end
    endcase
  end

  always_comb begin
    STORE_WMASK = misaligned_store ? 0 : wmask;
    STORE_TRAP_MCAUSE = misaligned_store ? TRAP_CODE_STORE_ADDR_MISALIGNED : 0;
    STORE_TRAP_VALID = misaligned_store;
  end

endmodule
