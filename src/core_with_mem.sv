module core_with_mem(
    input logic clk,rst,
    output logic [31:0] WriteData, DataAdr,
    output logic [1:0] MemWrite
  );
  logic [1:0] MemWrite_sig;
  logic [31:0] WriteData_sig, DataAdr_sig;
  logic [31:0] PCF,InstrF,ReadDataMTick;
  dtcore32_top riscv(
                   //inputs
                   .clk(clk),
                   .rst(rst),
                   .InstrF(InstrF),
                   .ReadDataMTick(ReadDataMTick),
                   //outputs
                   .PCF(PCF),
                   .ALUResultM(DataAdr_sig),
                   .WriteDataM(WriteData_sig),
                   .MemWriteM(MemWrite_sig)
                 );
  imem imem1(
         .a(PCF),
         .rd(InstrF)
       );
  dmem dmem1(
         .clk(clk),
         .we(MemWrite_sig),
         .a(DataAdr_sig),
         .wd(WriteData_sig),
         .rd(ReadDataMTick)
       );
assign WriteData = WriteData_sig;
assign DataAdr = DataAdr_sig;
assign MemWrite = MemWrite_sig;
endmodule


