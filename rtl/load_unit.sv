module load_unit
  import params_pkg::*;
(
  input logic [2:0] load_type,
  input logic [1:0] addr_lsb2,
  input logic [31:0] rdata_unformatted_i,
  output logic load_trap_o,
  output [30:0] load_trap_code_o,
  output logic [3:0] rmask_o,
  output logic [31:0] rdata_formatted_o
);

  logic misaligned_load;
  logic [3:0] rmask;
  logic [31:0] rdata_formatted;
  // logic to determine which bits of the read data from data memory will be loaded for load instructions
  always_comb begin
    misaligned_load = 0;
    rdata_formatted = 0;
    rmask = 4'h0;
    case (load_type)
      //lw
      DMEM_LOAD_SIZE_WORD: begin
        rdata_formatted = rdata_unformatted_i;
        rmask = 4'hf;
      end
      //lb
      DMEM_LOAD_SIZE_BYTE: begin
        rmask = 4'h1;
        unique case (addr_lsb2)
          2'b00: rdata_formatted = {{24{rdata_unformatted_i[7]}}, rdata_unformatted_i[7:0]};
          2'b01: rdata_formatted = {{24{rdata_unformatted_i[15]}}, rdata_unformatted_i[15:8]};
          2'b10: rdata_formatted = {{24{rdata_unformatted_i[23]}}, rdata_unformatted_i[23:16]};
          2'b11: rdata_formatted = {{24{rdata_unformatted_i[31]}}, rdata_unformatted_i[31:24]};
        endcase
      end
      //lbu
      DMEM_LOAD_SIZE_BYTEU: begin
        rmask = 4'h1;
        unique case (addr_lsb2)
          2'b00: begin
            rdata_formatted = {{24{1'b0}}, rdata_unformatted_i[7:0]};
            
          end
          2'b01: begin
            rdata_formatted = {{24{1'b0}}, rdata_unformatted_i[15:8]};
          end
          2'b10: begin
            rdata_formatted = {{24{1'b0}}, rdata_unformatted_i[23:16]};
          end
          2'b11: begin
            rdata_formatted = {{24{1'b0}}, rdata_unformatted_i[31:24]};
          end
        endcase
      end
      //lh
      DMEM_LOAD_SIZE_HALF: begin
        rmask = 4'h3;
        case (addr_lsb2[1])
          //2'b00: begin
            0:
            rdata_formatted = {{16{rdata_unformatted_i[15]}}, rdata_unformatted_i[15:0]};
          //2'b10: begin
            1:
            rdata_formatted = {{16{rdata_unformatted_i[31]}}, rdata_unformatted_i[31:16]};
          //default: misaligned_load = 1;
        endcase
      end
      //lhu
      DMEM_LOAD_SIZE_HALFU: begin
        rmask = 4'h3;
        case (addr_lsb2[1])
          //2'b00: begin
          0:
            rdata_formatted = {{16{1'b0}}, rdata_unformatted_i[15:0]};

          //2'b10: begin
          1:
            rdata_formatted = {{16{1'b0}}, rdata_unformatted_i[31:16]};

          //default: misaligned_load = 1;
        endcase
      end
      default:;
    endcase
  end
  assign rmask_o           = misaligned_load ? 0 : rmask;
  assign rdata_formatted_o = rdata_formatted;
  assign load_trap_code_o       = misaligned_load ? TRAP_CODE_LOAD_ADDR_MISALIGNED :
    0;

  assign load_trap_o = misaligned_load;
endmodule
