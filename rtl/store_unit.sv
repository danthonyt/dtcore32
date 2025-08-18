module store_unit
  import params_pkg::*;
(
    input logic en,
    input logic [1:0] store_size_i,
    input logic [1:0] addr_lsb2_i,
    input logic [31:0] wdata_unformatted_i,
    output logic store_trap_o,
    output logic [30:0] trap_code_o,
    output logic [3:0] wmask_o,
    output logic [31:0] wdata_formatted_o
);

  logic misaligned_store;
  logic [31:0] wdata_formatted;
  logic [3:0] wmask;
  always_comb begin
    misaligned_store = 0;
    wdata_formatted = 0;
    wmask = 4'h0;
    if (en) begin
      unique case (store_size_i)
        MEM_NO_DMEM_WR: begin
        end
        MEM_WORD_WR: begin
          wmask = 4'hf;
          wdata_formatted = wdata_unformatted_i;
        end
        MEM_HALF_WR: begin
          case (addr_lsb2_i)
            2'b10: begin
              wmask = 4'hc;
              wdata_formatted = {wdata_unformatted_i[15:0], 16'd0};
            end
            2'b00: begin 
              wmask = 4'h3;
              wdata_formatted = {16'd0, wdata_unformatted_i[15:0]};
            end
            default: begin
              wmask = 'x;
              wdata_formatted = 'x;
            end
          endcase
        end
        MEM_BYTE_WR: begin
          case (addr_lsb2_i)
            2'b00: begin
              wmask = 4'h1;
              wdata_formatted = {24'd0, wdata_unformatted_i[7:0]};
            end
            2'b01: begin
              wmask = 4'h2;
              wdata_formatted = {16'd0, wdata_unformatted_i[7:0], 8'd0};
            end
            2'b10: begin
              wmask = 4'h4;
              wdata_formatted = {8'd0, wdata_unformatted_i[7:0], 16'd0};
            end
            2'b11: begin
              wmask = 4'h8;
              wdata_formatted = {wdata_unformatted_i[7:0], 24'd0};
            end 
            default: begin
              wmask = 'x;
              wdata_formatted = 'x;
            end
          endcase
        end
      endcase
    end
  end

  always_comb begin
    wdata_formatted_o = wdata_formatted;
    wmask_o = misaligned_store ? 0 : wmask;
    trap_code_o = misaligned_store ? TRAP_CODE_STORE_ADDR_MISALIGNED : 0;
    store_trap_o = misaligned_store;
  end

endmodule
