module load_unit
  import params_pkg::*;
(
    input mem_op_t MEM_OP,
    input logic [1:0] ADDR_LSB2,
    input logic [31:0] RDATA_RAW,
    output logic LOAD_TRAP_VALID,
    output [30:0] LOAD_TRAP_MCAUSE,
    output logic [3:0] LOAD_RMASK,
    output logic [31:0] LOAD_FORMATTED
);
  logic [31:0] loaded;
  logic misaligned_load;
  logic [3:0] rmask;
  logic [31:0] load_formatted;
  assign loaded = RDATA_RAW >> 8 * (ADDR_LSB2);
  // logic to determine which bits of the read data from data memory will be loaded for load instructions
  always_comb begin
    misaligned_load = 0;
    rmask = 4'h0;
    load_formatted = 32'd0;
    case (MEM_OP)
      //lw
      MEM_LW: begin
        rmask = 4'hf;
        load_formatted = RDATA_RAW;
      end
      //lb
      MEM_LB: begin
        rmask = 4'h1;
        load_formatted = {{24{RDATA_RAW[7]}}, RDATA_RAW[7:0]};
      end
      //lbu
      MEM_LBU: begin
        rmask = 4'h1;
        load_formatted = {{24{1'b0}}, RDATA_RAW[7:0]};
      end
      //lh
      MEM_LH: begin
        rmask = 4'h3;
        load_formatted = {{16{RDATA_RAW[15]}}, RDATA_RAW[15:0]};
      end
      //lhu
      MEM_LHU: begin
        rmask = 4'h3;
        load_formatted = {{16{1'b0}}, RDATA_RAW[15:0]};
      end
      default: ;
    endcase
  end
  assign LOAD_RMASK       = misaligned_load ? 0 : rmask;
  assign LOAD_TRAP_MCAUSE = misaligned_load ? TRAP_CODE_LOAD_ADDR_MISALIGNED : 0;
  assign LOAD_TRAP_VALID  = misaligned_load;
  assign LOAD_FORMATTED = load_formatted;
endmodule
