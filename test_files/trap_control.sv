module trap_control
	import params_pkg::*;
(
    // IF
	input logic [31:0] IF_pc_i,
	input logic [31:0] ID_pc_i,
	input logic [31:0] EX_pc_i,
	input logic [31:0] MEM1_pc_i,
	input logic [31:0] MEM2_pc_i,
	// traps generated from a previous stage
	input trap_info_t ID_carried_trap_i,
	input trap_info_t EX_carried_trap_i,
	input trap_info_t MEM1_carried_trap_i,
	input trap_info_t MEM2_carried_trap_i,
	input trap_info_t WB_carried_trap_i,
	// trap data
	input logic main_decoder_trap_valid_i,
	input trap_code_e main_decoder_trap_code_i,
	input logic alu_decoder_trap_valid_i,
	input trap_code_e alu_decoder_trap_code_i,
	input logic store_trap_valid_i,
	input trap_code_e store_trap_code_i,
	input logic load_trap_valid_i,
	input trap_code_e load_trap_code_i,
	input logic jump_branch_trap_valid_i,
	input trap_code_e jump_branch_trap_code_i,
	// traps generated in their respective stage
	output trap_info_t IF_trap_o,
	output trap_info_t ID_trap_o,
	output trap_info_t EX_trap_o,
	output trap_info_t MEM1_trap_o,
	output trap_info_t MEM2_trap_o,
	output trap_info_t WB_trap_o
);

	assign IF_trap_o = (!(IF_pc_i[1] || IF_pc_i[0])) ?
		'{1, 0, TRAP_CODE_INSTR_ADDR_MISALIGNED, IF_pc_i}
		: trap_info_t'(ZERO_TRAP);

	assign ID_trap_o = ID_carried_trap_i.valid ? ID_carried_trap_i :
		main_decoder_trap_valid_i ? '{1, 0, main_decoder_trap_code_i, ID_pc_i} :
		alu_decoder_trap_valid_i ? '{1, 0, alu_decoder_trap_code_i, ID_pc_i} :
		trap_info_t'(ZERO_TRAP);

	assign EX_trap_o = EX_carried_trap_i.valid ? EX_carried_trap_i :
		jump_branch_trap_valid_i ? '{1, 0, TRAP_CODE_INSTR_ADDR_MISALIGNED, EX_pc_i} :
		trap_info_t'(ZERO_TRAP);

	assign MEM1_trap_o = MEM1_carried_trap_i.valid ? MEM1_carried_trap_i :
		store_trap_valid_i ? '{1, 0, store_trap_code_i, MEM1_pc_i} :
		trap_info_t'(ZERO_TRAP);

	assign MEM2_trap_o = MEM2_carried_trap_i.valid ? MEM2_carried_trap_i :
		load_trap_valid_i ? '{1, 0, load_trap_code_i, MEM2_pc_i} :
		trap_info_t'(ZERO_TRAP);

	assign WB_trap_o = WB_carried_trap_i.valid ? WB_carried_trap_i :
		trap_info_t'(ZERO_TRAP);

endmodule : trap_control