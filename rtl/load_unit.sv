module load_unit
  import params_pkg::*;
(
    input logic [4:0] MEM_OP,
    input logic [1:0] ADDR_LSB2,
    input logic [31:0] AXIL_RDATA,
    output logic LOAD_TRAP_VALID,
    output [30:0] LOAD_TRAP_MCAUSE,
    output logic [3:0] LOAD_RMASK,
    output logic [31:0] LOAD_FORMATTED
);
  logic [31:0] loaded;
  logic misaligned_load;
  logic [3:0] rmask;
  assign loaded = AXIL_RDATA >> 8 * (ADDR_LSB2);
  // logic to determine which bits of the read data from data memory will be loaded for load instructions
  always_comb begin
    misaligned_load = 0;
    rmask = 4'h0;
    LOAD_FORMATTED = 32'd0;
    case (MEM_OP)
      //lw
      MEM_LW: begin
        rmask = 4'hf;
        LOAD_FORMATTED = AXIL_RDATA;
      end
      //lb
      MEM_LB: begin
        rmask = 4'h1;
        LOAD_FORMATTED = {{24{AXIL_RDATA[7]}}, AXIL_RDATA[7:0]};
      end
      //lbu
      MEM_LBU: begin
        rmask = 4'h1;
        LOAD_FORMATTED = {{24{0}}, AXIL_RDATA[7:0]};
      end
      //lh
      MEM_LH: begin
        rmask = 4'h3;
        LOAD_FORMATTED = {{16{AXIL_RDATA[15]}}, AXIL_RDATA[15:0]};
      end
      //lhu
      MEM_LHU: begin
        rmask = 4'h3;
        LOAD_FORMATTED = {{16{0}}, AXIL_RDATA[15:0]};
      end
      default: ;
    endcase
  end
  assign LOAD_RMASK       = misaligned_load ? 0 : rmask;
  assign LOAD_TRAP_MCAUSE = misaligned_load ? TRAP_CODE_LOAD_ADDR_MISALIGNED : 0;
  assign LOAD_TRAP_VALID  = misaligned_load;
endmodule
