module alu_tb ();
  parameter WIDTH = 32;
  parameter OPS = 13;
  logic [3:0] control;
  logic [WIDTH-1:0] a;
  logic [WIDTH-1:0] b;
  logic [WIDTH-1:0] y;
  logic BranchCond;
  alu #(.WIDTH(WIDTH)) i_alu 
      (.control(control),
       .a(a),
       .b(b),
       .y(y),
       .BranchCond(BranchCond)
      );

  initial
  begin
        repeat(10000)
        begin
          control = $urandom % 13;
		  a = $urandom;
		  b = $urandom;
          #5;
          case (control)
            //add,addi,lw,sw
            4'b0000:
            begin
              assert(y == a + b) else
                $fatal("Incorrect sum.");
              assert(BranchCond == 1'b0) else
                $fatal("BranchCond asserted for ADD,LW, or SW instruction");
            end
            //sub,beq
            4'b0001:
            begin
              assert(y == a - b) else
                $fatal("Incorrect difference.");
              if (y)
                assert(BranchCond == 1'b0) else
                  $fatal("BranchCond deasserted for equal : beq");
              else
                assert(BranchCond == 1'b1) else
                  $fatal("BranchCond asserted for not equal : beq");
            end
            //and,andi
            4'b0010:
            begin
              assert(y == (a & b)) else
                $fatal("Incorrect bitwise AND.");
              assert(BranchCond == 1'b0) else
                $fatal("BranchCond asserted for AND operation");
            end
            //or,ori
            4'b0011:
            begin
              assert(y == a | b) else
                $fatal("Incorrect bitwise OR.");
              assert(BranchCond == 1'b0) else
                $fatal("BranchCond asserted for OR operation");
            end
            //sll,slli
            4'b0100:
            begin
              assert(y == a << b) else
                $fatal("Incorrect logical shift left.");
              assert(BranchCond == 1'b0) else
                $fatal("BranchCond asserted for shift left operation");
            end
            //slt,slti
            4'b0101:
            begin
              assert(y == $signed(a) < $signed(b)) else
                $fatal("Incorrect set less than signed result");
              if (y)
                assert(BranchCond == 1'b1) else
                  $fatal("incorrect BranchCond state for set less than signed instruction");
              else
                assert(BranchCond == 1'b0) else
                  $fatal("incorrect BranchCond state for set less than signed instruction");
            end
            //sltu,bltu
            4'b0110:
            begin
              assert(y == a < b) else
                $fatal("Incorrect set less than unsigned result");
              if (y)
                assert(BranchCond == 1'b1) else
                  $fatal("incorrect BranchCond state for set less than unsigned instruction");
              else
                assert(BranchCond == 1'b0) else
                  $fatal("incorrect BranchCond state for set less than unsigned instruction");
            end
            //xor,xori
            4'b0111:
            begin
              assert(y == a ^ b) else
                $fatal("Incorrect xor operation result.");
              assert(BranchCond == 1'b0) else
                $fatal("BranchCond asserted for xor operation");
            end
            //sra,srai
            4'b1000:
            begin
              assert(y == a >>> b) else
                $fatal("Incorrect arithmetic shift right result.");
              assert(BranchCond == 1'b0) else
                $fatal("BranchCond asserted for arithmetic shift right operation");
            end
            //srl,srli
            4'b1001:
            begin
              assert(y == a >> b) else
                $fatal("Incorrect logical shift right result.");
              assert(BranchCond == 1'b0) else
                $fatal("BranchCond asserted for logical shift right operation");
            end
            //bge
            4'b1010:
            begin
              assert(y == $signed(a) >= $signed(b)) else
                $fatal("Incorrect signed branch greater than or equal to result");
              if (y)
                assert(BranchCond == 1'b1) else
                  $fatal("incorrect BranchCond state for signed branch greater than or equal to  instruction");
              else
                assert(BranchCond == 1'b0) else
                  $fatal("incorrect BranchCond state for signed branch greater than or equal to  instruction");
            end
            //bgeu
            4'b1011:
            begin
              assert(y == a >= b) else
                $fatal("Incorrect unsigned branch greater than or equal to result");
              if (y)
                assert(BranchCond == 1'b1) else
                  $fatal("incorrect BranchCond state for unsigned branch greater than or equal to  instruction");
              else
                assert(BranchCond == 1'b0) else
                  $fatal("incorrect BranchCond state for unsigned branch greater than or equal to  instruction");
            end
            //bne
            4'b1100:
            begin
              assert(y == a - b) else
                $fatal("Incorrect branch not equal result");
              if (y)
                assert(BranchCond == 1'b1) else
                  $fatal("incorrect BranchCond state for branch not equal instruction");
              else
                assert(BranchCond == 1'b0) else
                  $fatal("incorrect BranchCond state for branch not equal instruction");
            end
          endcase
        end
		$display("ALL TESTS PASSED");
		$finish;
      end

endmodule :
alu_tb