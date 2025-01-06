module dtcore32_WB_stage(
	input logic  [1:0]  ResultSrcW,
	input logic  [31:0] ALUResultW, ReadDataW, PCPlus4W,
	//connects to execute and decode stage
	output logic [31:0] ResultW
);
	assign ResultW = ResultSrcW[1] ? PCPlus4W : (ResultSrcW[0] ? ReadDataW : ALUResultW); 
endmodule

