import riscv_pkg::*;
module alu(
    input logic [ALU_CTRL_T_WIDTH-1:0] alu_control,
    input logic [31:0] a,
    input logic [31:0] b,
    output logic bcond,
    output logic [31:0] alu_result
);
    
// calculates the branch condition of the instruction
  always_comb begin
    case (alu_control)
      SUB_ALU_CONTROL : bcond = (a == b);  // beq
      NE_ALU_CONTROL  : bcond = (a != b);
      LT_ALU_CONTROL  : bcond = ($signed(a) < $signed(b));
      LTU_ALU_CONTROL : bcond = (a < b);
      GE_ALU_CONTROL  : bcond = ($signed(a) >= $signed(b));
      GEU_ALU_CONTROL : bcond = (a >= b);
      default         : bcond = 0;
    endcase
  end

  // calculates the result of the instruction
  always_comb begin
    case (alu_control)
      ADD_ALU_CONTROL       : alu_result = a + b;
      SUB_ALU_CONTROL       : alu_result = a - b;
      AND_ALU_CONTROL       : alu_result = a & b;
      OR_ALU_CONTROL        : alu_result = a | b;
      XOR_ALU_CONTROL       : alu_result = a ^ b;
      LT_ALU_CONTROL, LTU_ALU_CONTROL: alu_result = {31'd0, bcond};
      L_SHIFT_ALU_CONTROL   : alu_result = a << b[4:0];
      R_SHIFT_L_ALU_CONTROL : alu_result = a >> b[4:0];
      R_SHIFT_A_ALU_CONTROL : alu_result = $signed(a) >>> b[4:0];
      default               : alu_result = 0;
    endcase
  end

endmodule
