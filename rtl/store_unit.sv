module store_unit
  import params_pkg::*;
(
    input logic [4:0] MEM_OP,
    input logic [1:0] ADDR_LSB2,
    input logic [31:0] STORE_WDATA_UNFORMATTED,
    output logic STORE_TRAP_VALID,
    output logic [30:0] STORE_TRAP_MCAUSE,
    output logic [3:0] STORE_WMASK,
    output logic [31:0] STORE_WDATA
);

  logic misaligned_store;
  logic [31:0] wdata_formatted;
  logic [3:0] wmask;
  always_comb begin
    misaligned_store = 0;
    wdata_formatted = 0;
    wmask = 4'h0;
    case (MEM_OP)
      MEM_SW: begin
        wmask = 4'b1111;
        wdata_formatted = STORE_WDATA_UNFORMATTED;
      end
      MEM_SH: begin
        wmask = 4'b11 << (ADDR_LSB2);
        wdata_formatted = STORE_WDATA_UNFORMATTED[15:0] << (8 * ADDR_LSB2);
      end
      MEM_SB: begin
        wmask = 4'b1 << ADDR_LSB2;
        wdata_formatted = STORE_WDATA_UNFORMATTED[7:0] << (8 * ADDR_LSB2);
      end
    endcase
  end

  always_comb begin
    STORE_WDATA = wdata_formatted;
    STORE_WMASK = misaligned_store ? 0 : wmask;
    STORE_TRAP_MCAUSE = misaligned_store ? TRAP_CODE_STORE_ADDR_MISALIGNED : 0;
    STORE_TRAP_VALID = misaligned_store;
  end

endmodule
