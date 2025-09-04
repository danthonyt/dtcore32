module store_unit
  import params_pkg::*;
(
    input mem_op_t MEM_OP,
    input logic [1:0] ADDR_LSB2,
    input logic [31:0] STORE_WDATA_RAW,
    output logic STORE_TRAP_VALID,
    output logic [30:0] STORE_TRAP_MCAUSE,
    output logic [3:0] WMASK,
    output logic [31:0] STORE_WDATA_FORMATTED
);

  logic misaligned_store;
  logic [3:0] wmask;
  logic [31:0] store_wdata_formatted;
  always_comb begin
    misaligned_store = 0;
    store_wdata_formatted = 0;
    wmask = 0;
    case (MEM_OP)
      MEM_SW: begin
        wmask = 4'hf;
        store_wdata_formatted = STORE_WDATA_RAW;
      end
      MEM_SH: begin
        wmask = 4'h3 << ADDR_LSB2[1] * 2;
        store_wdata_formatted = STORE_WDATA_RAW << ADDR_LSB2[1] * 16;
      end
      MEM_SB: begin
        wmask = 4'b1 << ADDR_LSB2;
        store_wdata_formatted = STORE_WDATA_RAW << ADDR_LSB2 * 8;
      end
      default:;
    endcase
  end

  assign WMASK = misaligned_store ? 0 : wmask;
  assign STORE_TRAP_MCAUSE = misaligned_store ? TRAP_CODE_STORE_ADDR_MISALIGNED : 0;
  assign STORE_TRAP_VALID = misaligned_store;
  assign STORE_WDATA_FORMATTED = misaligned_store ? 0 : store_wdata_formatted;

endmodule
