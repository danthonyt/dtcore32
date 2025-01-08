module dtcore32_ID_stage(
    input logic   		clk,rst,
    //control signals from hazard unit output
    input logic   		FlushE,
    //control signals from Writeback output
    input logic   		RegWriteW,
    //data signals from ifid register output
    input logic   [31:0] 	InstrD,PCD,PCPlus4D,
    //data signals from Writeback output
    input logic   [31:0]	ResultW,
    input logic   [4:0]   RdW,
    //ID/IE register outputs

    //to Execute stage
    output logic   [31:0]	RD1E,RD2E,PCE,ImmExtE,PCPlus4E,
    //to hazard unit
    output logic   [4:0] 	Rs1E,Rs2E,RdE,
    //to execute stage control
    output logic  	     	RegWriteE,JumpE,BranchE,ALUBSrcE,PCTargetALUSrcE,
    output logic   [1:0] 	ResultSrcE,MemWriteE,ALUASrcE,
    output logic   [2:0] 	LoadSizeE,
    output logic   [3:0] 	ALUControlE,
    output logic exception
  );
  //datapath outputs to ID/IE register input
  logic  [31:0]	RD1D,RD2D,ImmExtD,ImmExtD_sig;

  //control unit outputs to ID/IE register input
  logic 	   	RegWriteD,JumpD,BranchD,ALUBSrcD,PCTargetALUSrcD;
  logic  [1:0] ResultSrcD,MemWriteD,ALUASrcD;
  logic  [2:0] LoadSizeD;
  logic  [3:0] ALUControlD;
  //control unit to extend unit
  logic  [2:0] ImmSrcD;

  logic [4:0] RdD;
  logic [4:0] Rs1D,Rs2D;
  // instruction is addi x0, x0 , 0 for a nop
  logic isNop;
  assign RdD = isNop ? 0 : InstrD[11:7];
  assign Rs1D = isNop ? 0 : InstrD[19:15];
  assign Rs2D = isNop ? 0 : InstrD[24:20];
  // regfile source registers
  logic [4:0] a1,a2;
  assign a1 = isNop ? 0 : InstrD[19:15];
  assign a2 = isNop ? 0 : InstrD[24:20];
  assign ImmExtD = isNop ? 0 : ImmExtD_sig;
  dtcore32_controller control(
                        //inputs
                        .clk(clk),
                        .rst(rst),
                        .op(InstrD[6:0]),
                        .funct3(InstrD[14:12]),
                        .funct7b5(InstrD[30]),
                        //outputs
                        .ResultSrcD(ResultSrcD),
                        .ALUControlD(ALUControlD),
                        .ImmSrcD(ImmSrcD),
                        .ALUASrcD(ALUASrcD),
                        .ALUBSrcD(ALUBSrcD),
                        .MemWriteD(MemWriteD),
                        .RegWriteD(RegWriteD),
                        .JumpD(JumpD),
                        .BranchD(BranchD),
                        .LoadSizeD(LoadSizeD),
                        .PCTargetALUSrcD(PCTargetALUSrcD),
                        .isNop(isNop),
                        .exception(exception)
                      );
  dtcore32_regfile regfile1(
                     .clk(clk),
                     .we3(RegWriteW),
                     .rst(rst),
                     .a1(a1),
                     .a2(a2),
                     .a3(RdW),
                     .wd3(ResultW),
                     .rd1(RD1D),
                     .rd2(RD2D)
                   );

  // extend
  always_comb
  begin
    case (ImmSrcD)
      3'b000:
        ImmExtD_sig = { {20{InstrD[31]}}, InstrD[31:20] }; 				    		     //I-type ALU
      3'b001:
        ImmExtD_sig = { {20{InstrD[31]}}, InstrD[31:25], InstrD[11:7] }; 		     	 //S-type
      3'b010:
        ImmExtD_sig = { {20{InstrD[31]}}, InstrD[7], InstrD[30:25], InstrD[11:8], 1'b0};   //B-type
      3'b011:
        ImmExtD_sig = { {12{InstrD[31]}}, InstrD[19:12], InstrD[20], InstrD[30:21], 1'b0}; //J-type
      3'b100:
        ImmExtD_sig = { {27{1'b0}}, InstrD[24:20]};						                 //I-type Shift
      3'b101:
        ImmExtD_sig = { InstrD[31:12] , {12{1'b0}} };//U-type lui
      default:
        ImmExtD_sig = 0;
    endcase
  end


  always_ff@(posedge clk)
  begin
    if (FlushE || rst) begin
      RegWriteE <= 0;
      MemWriteE <= 0;
      JumpE <= 0;
      BranchE <= 0;
      ALUASrcE <= 0;
      ALUBSrcE <= 1;
      ResultSrcE <= 0;
      ALUControlE <= 0;
      RD1E <= 0;
      RD2E <= 0;
      PCE <= 0;
      ImmExtE <= 0; 
      PCPlus4E <= 0;
      RdE <= 0;
      Rs1E <= 0;
      Rs2E <= 0;
      LoadSizeE <= 0;
      PCTargetALUSrcE <= 0;
    end
    else
      {RegWriteE, MemWriteE, JumpE, BranchE, ALUASrcE,
          ALUBSrcE, ResultSrcE, ALUControlE,
          RD1E, RD2E,PCE, ImmExtE, PCPlus4E, RdE, Rs1E, Rs2E,LoadSizeE,PCTargetALUSrcE} <= {RegWriteD, MemWriteD, JumpD, BranchD, ALUASrcD, ALUBSrcD,
              ResultSrcD, ALUControlD, RD1D, RD2D,
              PCD, ImmExtD, PCPlus4D, RdD, Rs1D, Rs2D,LoadSizeD,PCTargetALUSrcD};

  end
endmodule

