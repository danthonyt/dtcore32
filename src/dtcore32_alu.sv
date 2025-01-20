`include "macros.svh"
module dtcore32_alu #(parameter WIDTH=32)(
    input  logic  [3:0]       control,
    input  logic [WIDTH-1:0] a,b,
    output logic [WIDTH-1:0] alu_result,
    output logic branch_condition
  );

  always_comb
  begin
    case (control)
      `EX_ADD_ALU_CONTROL: alu_result = a + b;
      `EX_SUB_ALU_CONTROL: alu_result = a - b;
      `EX_AND_ALU_CONTROL: alu_result = a & b;
      `EX_OR_ALU_CONTROL: alu_result = a | b;
      `EX_XOR_ALU_CONTROL:  alu_result = a ^ b;
      `EX_LT_ALU_CONTROL,`EX_LTU_ALU_CONTROL: alu_result = {31'd0,branch_condition};
      `EX_L_SHIFT_ALU_CONTROL: alu_result = a << b[4:0];
      `EX_R_SHIFT_L_ALU_CONTROL: alu_result = a >> b[4:0];
      `EX_R_SHIFT_A_ALU_CONTROL: alu_result = $signed(a) >>> b[4:0];
      default: alu_result = 0; 
    endcase
  end

  always_comb
  begin
    case (control)
      `EX_SUB_ALU_CONTROL: branch_condition = (a == b) ? 1 : 0; // beq
      `EX_NE_ALU_CONTROL: branch_condition = (a != b) ? 1 : 0;
      `EX_LT_ALU_CONTROL: branch_condition = ($signed(a) < $signed(b)) ? 1 : 0;
      `EX_LTU_ALU_CONTROL: branch_condition = (a < b) ? 1 : 0;
      `EX_GE_ALU_CONTROL: branch_condition = ($signed(a) >= $signed(b)) ? 1 : 0;
      `EX_GEU_ALU_CONTROL: branch_condition = (a >= b) ? 1 : 0;
      default: branch_condition = 0; 
    endcase
  end
endmodule

