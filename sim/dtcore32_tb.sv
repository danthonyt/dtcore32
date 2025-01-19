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


module dtcore32_tb();

  logic         clk = 0;
  logic         rst;
  logic  [31:0] IMEM_data;
  logic  [31:0] DMEM_rd_data;

  logic [31:0] IMEM_addr;
  logic [31:0] DMEM_addr;
  logic [31:0] DMEM_addr_actual;

  logic [3:0]  DMEM_wr_byte_en;
  logic [31:0] DMEM_wr_data;
  logic        Exception;


  dtcore32  UUT (
              .clk_i(clk),
              .rst_i(rst),
              .IMEM_rd_data_i(IMEM_data),
              .DMEM_rd_data_i(DMEM_rd_data),
              .IMEM_addr_o(IMEM_addr),
              .DMEM_addr_o(DMEM_addr),
              .DMEM_wr_data_o(DMEM_wr_data),
              .DMEM_wr_byte_en_o(DMEM_wr_byte_en),
              .exception_o(Exception)
            );
  always#(10) clk = ~clk;
  assign DMEM_addr_actual = DMEM_addr - 32'h2000;
  parameter MEMORY_DEPTH  = 32'hFFF;
  // MEMORY SIMULATION
  //logic [31:0] MEMORY [0:MEMORY_DEPTH];
  logic [31:0] IMEM [0:MEMORY_DEPTH];
  logic [31:0] DMEM [0:MEMORY_DEPTH];
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
  assign IMEM_data = IMEM[IMEM_addr[31:2]];
  always_ff@(posedge clk)
  begin//write
    if (rst)
    begin
      //IMEM_data <= 0;
      DMEM_rd_data <= 0;
    end
    else
    begin
      //IMEM_data = MEMORY[IMEM_addr[31:2]];
      DMEM_rd_data <= DMEM[DMEM_addr_actual[31:2]];
      if (DMEM_wr_byte_en[0])
        DMEM[DMEM_addr_actual[31:2]][7:0]   <= DMEM_wr_data[7:0];
      if (DMEM_wr_byte_en[1])
        DMEM[DMEM_addr_actual[31:2]][15:8]   <= DMEM_wr_data[15:8];
      if (DMEM_wr_byte_en[2])
        DMEM[DMEM_addr_actual[31:2]][23:16]   <= DMEM_wr_data[23:16];
      if (DMEM_wr_byte_en[3])
        DMEM[DMEM_addr_actual[31:2]][31:24]   <= DMEM_wr_data[31:24];
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
        //MEMORY[i] = 0;
        DMEM[i] = 0;
        IMEM[i] = 0;
      end
      case(TESTID)

        // R-R [0:9]
        `RR_ADD:
        begin
          $readmemh("add.imem.mem", IMEM);
          $readmemh("add.dmem.mem", DMEM);
        end
        `RR_SUB:
        begin
          $readmemh("sub.imem.mem", IMEM);
          $readmemh("sub.dmem.mem", DMEM);
        end
        `RR_AND:
        begin
          $readmemh("and.imem.mem", IMEM);
          $readmemh("and.dmem.mem", DMEM);
        end
        `RR_OR:
        begin
          $readmemh("or.imem.mem", IMEM);
          $readmemh("or.dmem.mem", DMEM);
        end
        `RR_XOR:
        begin
          $readmemh("xor.imem.mem", IMEM);
          $readmemh("xor.dmem.mem", DMEM);
        end
        `RR_SLT:
        begin
          $readmemh("slt.imem.mem", IMEM);
          $readmemh("slt.dmem.mem", DMEM);
        end
        `RR_SLTU:
        begin
          $readmemh("sltu.imem.mem", IMEM);
          $readmemh("sltu.dmem.mem", DMEM);
        end
        `RR_SLL:
        begin
          $readmemh("sll.imem.mem", IMEM);
          $readmemh("sll.dmem.mem", DMEM);
        end
        `RR_SRL:
        begin
          $readmemh("srl.imem.mem", IMEM);
          $readmemh("srl.dmem.mem", DMEM);
        end
        `RR_SRA:
        begin
          $readmemh("sra.imem.mem", IMEM);
          $readmemh("sra.dmem.mem", DMEM);
        end

        // R-I [10:17]
        `I_ADDI:
        begin
          $readmemh("addi.imem.mem", IMEM);
          $readmemh("addi.dmem.mem", DMEM);
        end
        `I_ANDI:
        begin
          $readmemh("andi.imem.mem", IMEM);
          $readmemh("andi.dmem.mem", DMEM);
        end
        `I_ORI:
        begin
          $readmemh("ori.imem.mem", IMEM);
          $readmemh("ori.dmem.mem", DMEM);
        end
        `I_XORI:
        begin
          $readmemh("xori.imem.mem", IMEM);
          $readmemh("xori.dmem.mem", DMEM);
        end
        `I_SLTI:
        begin
          $readmemh("slti.imem.mem", IMEM);
          $readmemh("slti.dmem.mem", DMEM);
        end
        `I_SLLI:
        begin
          $readmemh("slli.imem.mem", IMEM);
          $readmemh("slli.dmem.mem", DMEM);
        end
        `I_SRLI:
        begin
          $readmemh("srli.imem.mem", IMEM);
          $readmemh("srli.dmem.mem", DMEM);
        end
        `I_SRAI:
        begin
          $readmemh("srai.imem.mem", IMEM);
          $readmemh("srai.dmem.mem", DMEM);
        end

        // Conditional Branches [18:23]
        `B_BEQ:
        begin
          $readmemh("beq.imem.mem", IMEM);
          $readmemh("beq.dmem.mem", DMEM);
        end
        `B_BNE:
        begin
          $readmemh("bne.imem.mem", IMEM);
          $readmemh("bne.dmem.mem", DMEM);
        end
        `B_BLT:
        begin
          $readmemh("blt.imem.mem", IMEM);
          $readmemh("blt.dmem.mem", DMEM);
        end
        `B_BGE:
        begin
          $readmemh("bge.imem.mem", IMEM);
          $readmemh("bge.dmem.mem", DMEM);
        end
        `B_BLTU:
        begin
          $readmemh("bltu.imem.mem", IMEM);
          $readmemh("bltu.dmem.mem", DMEM);
        end
        `B_BGEU:
        begin
          $readmemh("bgeu.imem.mem", IMEM);
          $readmemh("bgeu.dmem.mem", DMEM);
        end

        // Upper Imm [24:25]
        `UI_LUI:
        begin
          $readmemh("lui.imem.mem", IMEM);
          $readmemh("lui.dmem.mem", DMEM);
        end
        `UI_AUIPC:
        begin
          $readmemh("auipc.imem.mem", IMEM);
          $readmemh("auipc.dmem.mem", DMEM);
        end

        // Jumps [26:27]
        `J_JAL:
        begin
          $readmemh("jal.imem.mem", IMEM);
          $readmemh("jal.dmem.mem", DMEM);
        end
        `J_JALR:
        begin
          $readmemh("jalr.imem.mem", IMEM);
          $readmemh("jalr.dmem.mem", DMEM);
        end

        // Loads [28:32]
        `L_LB:
        begin
          $readmemh("lb.imem.mem", IMEM);
          $readmemh("lb.dmem.mem", DMEM);
        end
        `L_LH:
        begin
          $readmemh("lh.imem.mem", IMEM);
          $readmemh("lh.dmem.mem", DMEM);
        end
        `L_LW:
        begin
          $readmemh("lw.imem.mem", IMEM);
          $readmemh("lw.dmem.mem", DMEM);
        end
        `L_LBU:
        begin
          $readmemh("lbu.imem.mem", IMEM);
          $readmemh("lbu.dmem.mem", DMEM);
        end
        `L_LHU:
        begin
          $readmemh("lhu.imem.mem", IMEM);
          $readmemh("lhu.dmem.mem", DMEM);
        end

        // Stores [33:35]
        `S_SB:
        begin
          $readmemh("sb.imem.mem", IMEM);
          $readmemh("sb.dmem.mem", DMEM);
        end
        `S_SH:
        begin
          $readmemh("sh.imem.mem", IMEM);
          $readmemh("sh.dmem.mem", DMEM);
        end
        `S_SW:
        begin
          $readmemh("sw.imem.mem", IMEM);
          $readmemh("sw.dmem.mem", DMEM);
        end


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
           if((UUT.dtcore32_ID_stage_inst.dtcore32_regfile_inst.reg_array[3] == 1) &&
               (UUT.dtcore32_ID_stage_inst.dtcore32_regfile_inst.reg_array[17] == 93) &&
               (UUT.dtcore32_ID_stage_inst.dtcore32_regfile_inst.reg_array[10] == 0))
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
