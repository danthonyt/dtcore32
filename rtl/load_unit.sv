module load_unit
  import params_pkg::*;
(
    input logic [4:0] MEM_OP,
    input logic [1:0] ADDR_LSB2,
    output logic LOAD_TRAP_VALID,
    output [30:0] LOAD_TRAP_MCAUSE,
    output logic [3:0] LOAD_RMASK,
    output logic LOAD_IS_SIGNED
);

  logic misaligned_load;
  logic [3:0] rmask;
  logic is_signed;
  // logic to determine which bits of the read data from data memory will be loaded for load instructions
  always_comb begin
    misaligned_load = 0;
    rmask = 4'h0;
    is_signed = 0;
    case (MEM_OP)
      //lw
      MEM_LW: begin
        rmask = 4'hf;
        is_signed = 1;
      end
      //lb
      MEM_LB: begin
        rmask = 4'h1 << (8*ADDR_LSB2);
        is_signed = 1;
      end
      //lbu
      MEM_LBU: begin
        rmask = 4'h1 << (8*ADDR_LSB2);
        is_signed = 0;
      end
      //lh
      MEM_LH: begin
        rmask = 4'h3 << (8*ADDR_LSB2);
        is_signed = 1;
      end
      //lhu
      MEM_LHU: begin
        rmask = 4'h3 << (8*ADDR_LSB2);
        is_signed = 0;
      end
      default: ;
    endcase
  end
  assign LOAD_RMASK       = misaligned_load ? 0 : rmask;
  assign LOAD_TRAP_MCAUSE = misaligned_load ? TRAP_CODE_LOAD_ADDR_MISALIGNED : 0;
  assign LOAD_IS_SIGNED = is_signed;
  assign LOAD_TRAP_VALID  = misaligned_load;
endmodule
