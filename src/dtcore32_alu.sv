`include "macros.svh"
module dtcore32_alu #(parameter WIDTH=32)(
    input  logic  [3:0]       control,
    input  logic [WIDTH-1:0] a,b,
    output logic [WIDTH-1:0] y,
    output logic BranchCond
  );
  
  always_comb
  begin
    BranchCond = 0;
    case (control)
      //add,addi,lw,sw
      `EX_ADD_ALU_CONTROL:
        y = a + b;
      //sub,beq
      `EX_SUB_ALU_CONTROL:
      begin
        y = a - b;
        BranchCond = (y == 0) ? 1 : 0;
      end
      //and,andi
      `EX_AND_ALU_CONTROL:
        y = a & b;
      //or,ori
      `EX_OR_ALU_CONTROL:
        y = a | b;
      //sll,slli
      `EX_L_SHIFT_ALU_CONTROL:
        y = a << (b & 'h1f);

      //slt,slti,blt
      `EX_LT_ALU_CONTROL:
      begin
        y = ($signed(a) < $signed(b)) ? 1 : 0;
        BranchCond = (y == 0) ? 0 : 1;
      end
      //sltu,sltiu,bltu
      `EX_LTU_ALU_CONTROL:
      begin
        y = (a < b) ? 1 : 0;
        BranchCond = (y == 0) ? 0 : 1;
      end
      //xor,xori
      `EX_XOR_ALU_CONTROL:
        y = a ^ b;
      //sra,srai
      `EX_R_SHIFT_A_ALU_CONTROL:
        y = $signed(a) >>> (b & 'h1f);
      //srl,srli
      `EX_R_SHIFT_L_ALU_CONTROL:
        y = a >> (b & 'h1f);
      //bge
      `EX_GE_ALU_CONTROL:
      begin
        y = ($signed(a) >= $signed(b)) ? 1 : 0;
        BranchCond = (y == 0) ? 0 : 1;
      end
      //bgeu
      `EX_GEU_ALU_CONTROL:
      begin
        y = (a >= b) ? 1 : 0;
        BranchCond = (y == 0) ? 0 : 1;
      end
      //bne
      `EX_NE_ALU_CONTROL:
      begin
        y = a - b;
        BranchCond = (y == 0) ? 0 : 1;
      end
      default:
        y = 0; //??
    endcase
  end
endmodule

