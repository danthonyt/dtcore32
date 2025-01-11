module extend
(
    input logic [31:7] instr_data,
    input logic [2:0] imm_src,
    output logic [31:0] imm_ext
);
 // extend
always_comb
begin
  case (imm_src)
    3'b000:
      imm_ext = { {20{instr_data[31]}}, instr_data[31:20] }; 				    		     //I-type ALU
    3'b001:
      imm_ext = { {20{instr_data[31]}}, instr_data[31:25], instr_data[11:7] }; 		     	 //S-type
    3'b010:
      imm_ext = { {20{instr_data[31]}}, instr_data[7], instr_data[30:25], instr_data[11:8], 1'b0};   //B-type
    3'b011:
      imm_ext = { {12{instr_data[31]}}, instr_data[19:12], instr_data[20], instr_data[30:21], 1'b0}; //J-type
    3'b100:
      imm_ext = { {27{1'b0}}, instr_data[24:20]};						                 //I-type Shift
    3'b101:
      imm_ext = { instr_data[31:12] , {12{1'b0}} };//U-type lui
    default:
      imm_ext = 0;
  endcase
end
endmodule
