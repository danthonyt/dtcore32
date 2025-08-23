module mem_router 
import params_pkg::*;
(
    input logic [31:0] MEM_ALU_RESULT,
    input mem_op_t MEM_OP,
    output logic DMEM_EN,
    output logic AXIL_EN,
    output logic [31:0] AXIL_ADDR

);

  // dmem addresses 0x1000 - 0x13FF
  // axil addresses 0x2400 - 0x240F
  // decode address for axil transactions
  assign AXIL_ADDR = {24'd0, MEM_ALU_RESULT[3:0]};
  always_comb begin
    DMEM_EN = 0;
    AXIL_EN = 0;
    // enable DMEM if if in the correct address range AND is a load or store instruction
    if (((MEM_ALU_RESULT >= 32'h1000) && (MEM_ALU_RESULT < 32'h1400)) && (MEM_OP != MEM_NONE)) begin
      DMEM_EN = 1;
    // enable axil interface if in the correct address range AND is a LW or SW
    end else if (((MEM_ALU_RESULT >= 32'h2400) && (MEM_ALU_RESULT <= 32'h240F)) && ((MEM_OP == MEM_LW)  || (MEM_OP == MEM_SW))) begin
      AXIL_EN = 1;
    end 
  end
endmodule