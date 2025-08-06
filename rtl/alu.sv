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
			SUB_ALU_CONTROL: branch_cond = (a_i == b_i) ? 1 : 0;  // beq
			NE_ALU_CONTROL: branch_cond = (a_i != b_i) ? 1 : 0;
			LT_ALU_CONTROL: branch_cond = ($signed(a_i) < $signed(b_i)) ? 1 : 0;
			LTU_ALU_CONTROL: branch_cond = (a_i < b_i) ? 1 : 0;
			GE_ALU_CONTROL: branch_cond = ($signed(a_i) >= $signed(b_i)) ? 1 : 0;
			GEU_ALU_CONTROL: branch_cond = (a_i >= b_i) ? 1 : 0;
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

