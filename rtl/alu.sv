//===========================================================
// Project    : RISC-V CPU
// File       : alu.sv
// Module     : alu
// Description: alu for cpu instruction execution
//
// Inputs:
//   a_i       	    - first 32-bit operand 
//   b_i       		- second 32-bit operand
//   control_i   	- selects the alu operation executed
//
//
// Outputs:
//   branch_cond_o  - result of branch condition; 1 if 
//                    true and 0 if false
//	 result_o		- 32-bit result of alu operation
//
// Notes:
//   - supports ADD, SUB, AND, OR, XOR, left shift, and 
//     right shift (arithmetic and logical) operations
//   - supports equal, not equal, less than signed/unsigned,
//     and greater than or equal to signed/unsigned relational
//     operations
//     
//
// Author     : David Torres
// Date       : 2025-09-15
//===========================================================

module alu
	import params_pkg::*;
(
	input logic [31:0] a_i,
	input logic [31:0] b_i,
	input logic [3:0] control_i,
	output logic branch_cond_o,
	output logic [31:0] result_o
);

	logic [31:0] result;
	logic branch_cond;

// calculates the branch condition
	always_comb begin
		case (control_i)
			SUB_ALU_CONTROL: branch_cond = (a_i == b_i);  // beq
			NE_ALU_CONTROL: branch_cond = (a_i != b_i);
			LT_ALU_CONTROL: branch_cond = ($signed(a_i) < $signed(b_i));
			LTU_ALU_CONTROL: branch_cond = (a_i < b_i);
			GE_ALU_CONTROL: branch_cond = ($signed(a_i) >= $signed(b_i));
			GEU_ALU_CONTROL: branch_cond = (a_i >= b_i);
			default: branch_cond = 0;
		endcase
	end

	always_comb begin
		case (control_i)
			ADD_ALU_CONTROL: result = a_i + b_i;
			SUB_ALU_CONTROL: result = a_i - b_i;
			AND_ALU_CONTROL: result = a_i & b_i;
			OR_ALU_CONTROL: result = a_i | b_i;
			XOR_ALU_CONTROL: result = a_i ^ b_i;
			LT_ALU_CONTROL, LTU_ALU_CONTROL: result = {31'd0, branch_cond};
			L_SHIFT_ALU_CONTROL: result = a_i << b_i[4:0];
			R_SHIFT_L_ALU_CONTROL: result = a_i >> b_i[4:0];
			R_SHIFT_A_ALU_CONTROL: result = $signed(a_i) >>> b_i[4:0];
			default: result = 0;
		endcase
	end
	assign branch_cond_o = branch_cond;
	assign result_o      = result;
endmodule

