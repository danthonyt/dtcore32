module dtcore32_MEM_stage(
	input logic clk,rst,
	//inputs from IE/DM register
		//control
	input logic 	   	RegWriteM,
	input logic [1:0] 	ResultSrcM,
	input logic [2:0] 	LoadSizeM,
		//data
	input logic [31:0] 	ALUResultM, PCPlus4M,
	input logic [4:0]  	RdM,
	//input from data memory
	input logic [31:0] 	ReadDataMTick,
	//outputs from DM/WB register
	
	//connects to decode stage
	output logic   		RegWriteW,
	//connects to hazard unit and decode stage
	output logic   [4:0] 	RdW,
	//connects to writeback stage
	output logic   [1:0] 	ResultSrcW,
	output logic   [31:0] ALUResultW, ReadDataW, PCPlus4W
);
	logic [31:0] ReadDataM;
	logic [1:0] byte_num;
	assign byte_num = ALUResultM[1:0];
	
	always_comb begin
		case (LoadSizeM)
			//lw
			3'b000:	ReadDataM = ReadDataMTick;
			//lb
			3'b001:	case(byte_num)
					2'b00: ReadDataM = { {24{ReadDataMTick[7]}}, ReadDataMTick[7:0] };
					2'b01: ReadDataM = { {24{ReadDataMTick[15]}}, ReadDataMTick[15:8] };
					2'b10: ReadDataM = { {24{ReadDataMTick[23]}}, ReadDataMTick[23:16] };
					2'b11: ReadDataM = { {24{ReadDataMTick[31]}}, ReadDataMTick[31:24] };
				endcase
			//lbu
			3'b010:	case(byte_num)
					2'b00: ReadDataM = { {24{1'b0}},ReadDataMTick[7:0] };
					2'b01: ReadDataM = { {24{1'b0}},ReadDataMTick[15:8] };
					2'b10: ReadDataM = { {24{1'b0}},ReadDataMTick[23:16] };
					2'b11: ReadDataM = { {24{1'b0}},ReadDataMTick[31:24] };
				endcase
			
			//lh
			3'b011: case(byte_num[1])
					1'b0: ReadDataM = { {16{ReadDataMTick[15]}},ReadDataMTick[15:0] };
					1'b1: ReadDataM = { {16{ReadDataMTick[31]}},ReadDataMTick[31:16] };
				endcase
			
			//lhu
			3'b100: case(byte_num[1])
					1'b0: ReadDataM = { {16{1'b0}},ReadDataMTick[15:0] };
					1'b1: ReadDataM = { {16{1'b0}},ReadDataMTick[31:16] };
				endcase
				
			default:ReadDataM = 32'd0;
		endcase
	end
	always_ff@(posedge clk)
	begin
	  if(rst)
		{ALUResultW, ReadDataW, PCPlus4W, RdW,RegWriteW, ResultSrcW} <= 0;
	  else
		{ALUResultW, ReadDataW, PCPlus4W, RdW,RegWriteW, ResultSrcW} <= {ALUResultM, ReadDataM, PCPlus4M, RdM,RegWriteM, ResultSrcM};
	end
endmodule
