module alu #(parameter WIDTH=32)(
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
      4'b0000:
        y = a + b;
      //sub,beq
      4'b0001:
      begin
        y = a - b;
        BranchCond = (y == 0) ? 1 : 0; 
      end
      //and,andi
      4'b0010:
        y = a & b;
      //or,ori
      4'b0011:
        y = a | b;
      //sll,slli
      4'b0100:
        y = a << b;

      //slt,slti,blt
      4'b0101:
      begin
        y = ($signed(a) < $signed(b)) ? 1 : 0;
        BranchCond = (y == 0) ? 0 : 1; 
      end
      //sltu,sltiu,bltu
      4'b0110:
      begin
        y = (a < b) ? 1 : 0;
        BranchCond = (y == 0) ? 0 : 1; 
      end
      //xor,xori
      4'b0111:
        y = a ^ b;
      //sra,srai
      4'b1000:
        y = a >>> b;
      //srl,srli
      4'b1001:
        y = a >> b;
      //bge
      4'b1010:
      begin
        y = ($signed(a) >= $signed(b)) ? 1 : 0;
        BranchCond = (y == 0) ? 0 : 1; 
      end
      //bgeu
      4'b1011:
      begin
        y = (a >= b) ? 1 : 0;
        BranchCond = (y == 0) ? 0 : 1; 
      end
      //bne
      4'b1100:
      begin
        y = a - b;
        BranchCond = (y == 0) ? 0 : 1; 
      end
      default:
        y = 0; //??
    endcase
  end
endmodule

