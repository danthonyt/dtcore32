`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company:
// Engineer:
//
// Create Date: 07/12/2021 10:15:58 AM
// Design Name:
// Module Name: riscv-tests_tb
// Project Name:
// Target Devices:
// Tool Versions:
// Description:
//
// Dependencies:
//
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
//
//////////////////////////////////////////////////////////////////////////////////
//import   RV32I_definitions::*;

// Register-Register
`define RR_ADD   0
`define RR_SUB   1
`define RR_AND   2
`define RR_OR    3
`define RR_XOR   4
`define RR_SLT   5
`define RR_SLTU  6
`define RR_SLL   7
`define RR_SRL   8
`define RR_SRA   9

// Register-Immediate
`define I_ADDI   10
`define I_ANDI   11
`define I_ORI    12
`define I_XORI   13
`define I_SLTI   14
`define I_SLLI   15
`define I_SRLI   16
`define I_SRAI   17

// Conditional Branches
`define B_BEQ    18
`define B_BNE    19
`define B_BLT    20
`define B_BGE    21
`define B_BLTU   22
`define B_BGEU   23

// Upper Immediate
`define UI_LUI   24
`define UI_AUIPC 25

// Jumps
`define J_JAL    26
`define J_JALR   27

// Loads
`define L_LB     28
`define L_LH     29
`define L_LW     30
`define L_LBU    31
`define L_LHU    32

// Stores
`define S_SB     33
`define S_SH     34
`define S_SW     35

// INDIVIDUAL TEST TO RUN
`define TEST_TO_RUN 0


module testbench();

  logic         clk = 0;
  logic         rst;
  logic  [31:0] IMEM_data;
  logic  [31:0] DMEM_rd_data;

  logic [31:0] IMEM_addr;
  logic [31:0] DMEM_addr;
  logic [3:0]  DMEM_wr_byte_en;
  logic [31:0] DMEM_wr_data;
  logic        Exception;

  dtcore32_top UUT(
                 .clk(clk),
                 .rst(rst),
                 .InstrF(IMEM_data),
                 .ReadDataMTick(DMEM_rd_data),
                 .PCF(IMEM_addr),
                 .ALUResultM(DMEM_addr),
                 .WriteDataM(DMEM_wr_data),
                 .MemWriteM(DMEM_wr_byte_en),
                 .exception(Exception)
               );

  always#(10) clk = ~clk;


  // dump vcd?
  initial
  begin
    if($test$plusargs("vcd"))
    begin
      $dumpfile("testbench.vcd");
      $dumpvars(0, testbench);
    end
  end


  parameter MEMORY_DEPTH  = 32'hFFF;


  // MEMORY SIMULATION
  logic [31:0] MEMORY [0:MEMORY_DEPTH];
  /*
      $readmemh loads program data into consecutive addresses, however 
      RISC-V uses byte-addressable memory (i.e. a word at every fourth address)
      A workaround is to ignore the lower two bits of the address.
      Do this for both program data and data memory. 
   
      Note that program memory and data memory are loaded from the same .hex file.
      Data memory begins at 0x2000, this can be changed by editing /Scripts/memgen.sh and
      changing the -Tdata parameter of riscv32-unknown-elf-ld.
  */
  // Data memory and IMEM
	always_ff@(posedge clk) begin//write
	   if (rst)begin
	       IMEM_data <= 0;
         DMEM_rd_data <= 0;
	   end 
	   else begin
	    IMEM_data = MEMORY[IMEM_addr[31:2]];
      DMEM_rd_data <= MEMORY[DMEM_addr[31:2]];
		case(DMEM_wr_byte_en)
			//no write for 2'b00
			//sw
			2'b01: MEMORY[DMEM_addr[31:2]]<= DMEM_wr_data[31:0];
			//sh
			2'b10: case(DMEM_addr[1])
						1'b0:MEMORY[DMEM_addr[31:2]][15:0]<= DMEM_wr_data[15:0];
						1'b1:MEMORY[DMEM_addr[31:2]][31:16]<= DMEM_wr_data[15:0];
						default: MEMORY[DMEM_addr[31:2]]<= MEMORY[DMEM_addr[31:2]];
				   endcase
			//sb
			2'b11: case(DMEM_addr[1:0])
						2'b00:MEMORY[DMEM_addr[31:2]][7:0] <= DMEM_wr_data[7:0];
						2'b01:MEMORY[DMEM_addr[31:2]][15:8] <= DMEM_wr_data[7:0];
						2'b10:MEMORY[DMEM_addr[31:2]][23:16] <= DMEM_wr_data[7:0];
						2'b11:MEMORY[DMEM_addr[31:2]][31:24] <= DMEM_wr_data[7:0];
						default: MEMORY[DMEM_addr[31:2]]<= MEMORY[DMEM_addr[31:2]];
				   endcase 
				   
			default: MEMORY[DMEM_addr[31:2]]    <= MEMORY[DMEM_addr[31:2]];    
		endcase
	 end
  end
  //
  // SIMULATION TASKS
  //
  integer i;
  task LOAD_TEST;
    input integer TESTID;
    begin
      rst = 1;
      #10;
      for (i=0; i<= MEMORY_DEPTH; i=i+1)
      begin
        MEMORY[i] = 0;
      end
      case(TESTID)

        // R-R [0:9]
        `RR_ADD:
          $readmemh("add.mem"  ,MEMORY);
        `RR_SUB:
          $readmemh("sub.mem"  ,MEMORY);
        `RR_AND:
          $readmemh("and.mem"  ,MEMORY);
        `RR_OR:
          $readmemh("or.mem"   ,MEMORY);
        `RR_XOR:
          $readmemh("xor.mem"  ,MEMORY);
        `RR_SLT:
          $readmemh("slt.mem"  ,MEMORY);
        `RR_SLTU:
          $readmemh("sltu.mem" ,MEMORY);
        `RR_SLL:
          $readmemh("sll.mem"  ,MEMORY);
        `RR_SRL:
          $readmemh("srl.mem"  ,MEMORY);
        `RR_SRA:
          $readmemh("sra.mem"  ,MEMORY);

        // R-I [10:17]
        `I_ADDI:
          $readmemh("addi.mem" ,MEMORY);
        `I_ANDI:
          $readmemh("andi.mem" ,MEMORY);
        `I_ORI:
          $readmemh("ori.mem"  ,MEMORY);
        `I_XORI:
          $readmemh("xori.mem" ,MEMORY);
        `I_SLTI:
          $readmemh("slti.mem" ,MEMORY);
        `I_SLLI:
          $readmemh("slli.mem" ,MEMORY);
        `I_SRLI:
          $readmemh("srli.mem" ,MEMORY);
        `I_SRAI:
          $readmemh("srai.mem" ,MEMORY);

        // Conditional Branches [18:23]
        `B_BEQ:
          $readmemh("beq.mem"  ,MEMORY);
        `B_BNE:
          $readmemh("bne.mem"  ,MEMORY);
        `B_BLT:
          $readmemh("blt.mem"  ,MEMORY);
        `B_BGE:
          $readmemh("bge.mem"  ,MEMORY);
        `B_BLTU:
          $readmemh("bltu.mem" ,MEMORY);
        `B_BGEU:
          $readmemh("bgeu.mem" ,MEMORY);

        // Upper Imm [24:25]
        `UI_LUI:
          $readmemh("lui.mem"  ,MEMORY);
        `UI_AUIPC:
          $readmemh("auipc.mem",MEMORY);

        // Jumps [26:27]
        `J_JAL:
          $readmemh("jal.mem"  ,MEMORY);
        `J_JALR:
          $readmemh("jalr.mem" ,MEMORY);

        // Loads [28:32]
        `L_LB:
          $readmemh("lb.mem"   ,MEMORY);
        `L_LH:
          $readmemh("lh.mem"   ,MEMORY);
        `L_LW:
          $readmemh("lw.mem"   ,MEMORY);
        `L_LBU:
          $readmemh("lbu.mem"  ,MEMORY);
        `L_LHU:
          $readmemh("lhu.mem"  ,MEMORY);

        // Stores [33:35]
        `S_SB:
          $readmemh("sb.mem"   ,MEMORY);
        `S_SH:
          $readmemh("sh.mem"   ,MEMORY);
        `S_SW:
          $readmemh("sw.mem"   ,MEMORY);

      endcase
    end
  endtask // LOAD_TEST



  integer t;
  task EVAL_TEST;
    input integer TESTID;
    begin
      rst = 0;
      for(t=0; t<=1000000; t=t+1)
      begin
        @(posedge clk)
         begin

           // Check if test pass
           // pass condition: GP=1 , A7=93, A0=0
           if((UUT.decodestage.regfile1.rf[3] == 1) &&
               (UUT.decodestage.regfile1.rf[17] == 93) &&
               (UUT.decodestage.regfile1.rf[10] == 0))
           begin
             $display("TEST PASSED; ID: %0d", TESTID);
             t=1000000;

           end
           else if (Exception == 1)
           begin
             $display("EXCEPTION ASSERTED, TEST FAILED");
             $display("FAILED TEST ID: %0d", TESTID);
             $finish;

           end
           else if (t==999999)
           begin
             $display("TEST FAILED: TIMED OUT");
             $display("FAILED TEST ID: %0d", TESTID);
             $finish;
           end

         end
       end
     end
   endtask // EVAL_TEST


   //
   // TESTBENCH BEGIN
   //
   integer j;
  initial
  begin
    rst = 1;
    #100;

   // if($test$plusargs("runall"))
   if(1)
    begin
      $display("Running all tests.");
      for(j=`RR_ADD; j<=`S_SW; j=j+1)
      begin
        $display("***********************************");
        $display("Running Test ID: %0d", j);
        LOAD_TEST(j);
        #100;
        EVAL_TEST(j);

      end
      $display("");
      $display("***********************************");
      $display("ALL TESTS PASSED !");
      $finish;

    end

    else
    begin
      $display("Running Test ID: %0d", `TEST_TO_RUN);
      LOAD_TEST(`TEST_TO_RUN);
      EVAL_TEST(`TEST_TO_RUN);
      $display("***********************************");
      $display("TEST PASSED !");
      $finish;
    end
  end
endmodule
