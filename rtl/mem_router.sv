module mem_router #
(ADDR_WIDTH = 32
)(
    input logic [31:0] MEM1_ALU_RESULT,
    input logic [2:0] MEM1_MEM_LTYPE,
    input logic [1:0] MEM1_MEM_STYPE,
    output logic DMEM_EN,
    output logic AXIL_EN,
    output logic [31:0] AXIL_ADDR

);
import params_pkg::*;
  // dmem addresses 0x1000 - 0x13FF
  // axil addresses 0x2400 - 0x240F
  // decode address for axil transactions
  assign AXIL_ADDR = {24'd0, MEM1_ALU_RESULT[3:0]};
  always_comb begin
    DMEM_EN = 0;
    AXIL_EN = 0;
    // enable DMEM if if in the correct address range AND is a load or store instruction
    if (((MEM1_ALU_RESULT >= 32'h1000) && (MEM1_ALU_RESULT < 32'h1400)) && ((|MEM1_MEM_LTYPE) || (|MEM1_MEM_STYPE))) begin
      DMEM_EN = 1;
    // enable axil interface if in the correct address range AND is a LW or SW
    end else if (((MEM1_ALU_RESULT >= 32'h2400) && (MEM1_ALU_RESULT <= 32'h240F)) && ((MEM1_MEM_LTYPE == DMEM_LOAD_SIZE_WORD)  || (MEM1_MEM_STYPE == MEM_WORD_WR))) begin
      AXIL_EN = 1;
    end 
  end
endmodule