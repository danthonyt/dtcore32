module dtcore32_IF_stage(
    input logic 		clk,rst,
    //control signals from execute
    input logic  		PCSrcE,//set PC = PC + 4 or PcC Target
    //control signals fom hazard unit
    input logic 		StallF,//stall instruction fetch
    input logic 		StallD, FlushD,//stall and flush decode input
    //data signal from Writeback
    input logic  [31:0] PCTargetE,//next PC if branch or jump taken
    //instruction memory input
    input logic  [31:0] InstrF,//Instruction received from Instruction Memory
    //output to instruction memory
    output logic [31:0] PCF,//PC to receive instruction from Instruction Memory
    //IF/ID Register outputs
    output logic [31:0] InstrD,PCD,PCPlus4D//signals required for decode stage
  );
  logic [31:0] PCFTick, PCPlus4F;
  assign PCPlus4F = PCF + 32'd4;// Next instruction if no branch taken
  assign PCFTick = PCSrcE ? PCTargetE : PCPlus4F;
  always_ff@(posedge clk)
  begin
    if (rst)
      PCF <= 0;
    else if (!StallF)
      PCF <= PCFTick;
  end

  always_ff@(posedge clk)
  begin
    if (FlushD)
      {InstrD, PCD, PCPlus4D} <= 0;
    else if (rst)
      {InstrD, PCD, PCPlus4D} <= 0;
    else if (!StallD)
      {InstrD, PCD, PCPlus4D} <= {InstrF, PCF, PCPlus4F};
  end
endmodule

