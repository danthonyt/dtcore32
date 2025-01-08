module dtcore32_EX_stage(
    input logic   			clk,rst,
    //input from ID/IE register output

    //data signals
    input logic   [31:0]	RD1E,RD2E,PCE,ImmExtE,PCPlus4E,
    input logic   [4:0] 	RdE,
    //control signals
    input logic  	   		RegWriteE,JumpE,BranchE,ALUBSrcE,PCTargetALUSrcE,
    input logic   [1:0] 	ResultSrcE,MemWriteE,ALUASrcE,
    input logic   [2:0] 	LoadSizeE,
    input logic   [3:0] 	ALUControlE,
    //input from hazard unit
    input logic   [1:0] 	ForwardAE,ForwardBE,
    //forwarded inputs
    input logic   [31:0] 	ResultW,

    //connects to fetch stage
    output logic   [31:0] PCTargetE,
    //connects to fetch stage and hazard unit
    output logic   		PCSrcE,
    //connects to Data Memory stage
    output logic  	   	RegWriteM,
    output logic    [1:0] 	ResultSrcM,
    output logic    [2:0] 	LoadSizeM,
    output logic    [31:0] PCPlus4M,

    //connects to data memory
    output logic   [1:0] 	MemWriteM,
    output logic   [31:0]	WriteDataM,
    //connects to data memory,data memory stage, and execute stage
    output logic   [31:0] ALUResultM,
    //connects to data memory and hazard unit
    output logic   [4:0]  RdM
  );
// ===========================================================================
// 			          Parameters, Registers, and Wires
// ===========================================================================
  logic [31:0] SrcAETick,SrcAE,WriteDataE,SrcBE,PCTargetSrcAE, ALUResultE;
  logic 		 BranchCondE;

// ===========================================================================
// 			          Instantiations
// ===========================================================================
  dtcore32_alu #(.WIDTH(32)) alu1(//performs arithmetic calculations of instruction
        .a(SrcAE),
        .b(SrcBE),
        .control(ALUControlE),
        .y(ALUResultE),
        .BranchCond(BranchCondE)

      );
// ===========================================================================
// 			          Implementation
// ===========================================================================

  assign PCTargetE = PCTargetSrcAE + ImmExtE;	//adds branch offset to PC for B-type instructions
  assign PCSrcE = (BranchE & BranchCondE) | (JumpE);
  assign SrcBE = ALUBSrcE ? ImmExtE : WriteDataE;
  assign PCTargetSrcAE = PCTargetALUSrcE ? SrcAETick : PCE;
  assign SrcAETick = ForwardAE[1] ? ALUResultM : (ForwardAE[0] ? ResultW : RD1E); 
  assign WriteDataE = ForwardBE[1] ? ALUResultM : (ForwardBE[0] ? ResultW : RD2E); 
  assign SrcAE = ALUASrcE[1] ? PCE : (ALUASrcE[0] ? 0 : SrcAETick); 
  always_ff@(posedge clk)
  begin
    if(rst)
      {RegWriteM, MemWriteM, ResultSrcM, ALUResultM, WriteDataM, PCPlus4M, RdM, LoadSizeM} <= 0;

    else
      {RegWriteM, MemWriteM, ResultSrcM,
          ALUResultM, WriteDataM, PCPlus4M, RdM, LoadSizeM} <= {RegWriteE, MemWriteE, ResultSrcE,
              ALUResultE, WriteDataE, PCPlus4E, RdE, LoadSizeE};

  end
endmodule

