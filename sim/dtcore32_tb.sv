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
          $readmemh("add_imem.mem", IMEM);
          $readmemh("add_dmem.mem", DMEM);
        end
        `RR_SUB:
        begin
          $readmemh("sub_imem.mem", IMEM);
          $readmemh("sub_dmem.mem", DMEM);
        end
        `RR_AND:
        begin
          $readmemh("and_imem.mem", IMEM);
          $readmemh("and_dmem.mem", DMEM);
        end
        `RR_OR:
        begin
          $readmemh("or_imem.mem", IMEM);
          $readmemh("or_dmem.mem", DMEM);
        end
        `RR_XOR:
        begin
          $readmemh("xor_imem.mem", IMEM);
          $readmemh("xor_dmem.mem", DMEM);
        end
        `RR_SLT:
        begin
          $readmemh("slt_imem.mem", IMEM);
          $readmemh("slt_dmem.mem", DMEM);
        end
        `RR_SLTU:
        begin
          $readmemh("sltu_imem.mem", IMEM);
          $readmemh("sltu_dmem.mem", DMEM);
        end
        `RR_SLL:
        begin
          $readmemh("sll_imem.mem", IMEM);
          $readmemh("sll_dmem.mem", DMEM);
        end
        `RR_SRL:
        begin
          $readmemh("srl_imem.mem", IMEM);
          $readmemh("srl_dmem.mem", DMEM);
        end
        `RR_SRA:
        begin
          $readmemh("sra_imem.mem", IMEM);
          $readmemh("sra_dmem.mem", DMEM);
        end

        // R-I [10:17]
        `I_ADDI:
        begin
          $readmemh("addi_imem.mem", IMEM);
          $readmemh("addi_dmem.mem", DMEM);
        end
        `I_ANDI:
        begin
          $readmemh("andi_imem.mem", IMEM);
          $readmemh("andi_dmem.mem", DMEM);
        end
        `I_ORI:
        begin
          $readmemh("ori_imem.mem", IMEM);
          $readmemh("ori_dmem.mem", DMEM);
        end
        `I_XORI:
        begin
          $readmemh("xori_imem.mem", IMEM);
          $readmemh("xori_dmem.mem", DMEM);
        end
        `I_SLTI:
        begin
          $readmemh("slti_imem.mem", IMEM);
          $readmemh("slti_dmem.mem", DMEM);
        end
        `I_SLLI:
        begin
          $readmemh("slli_imem.mem", IMEM);
          $readmemh("slli_dmem.mem", DMEM);
        end
        `I_SRLI:
        begin
          $readmemh("srli_imem.mem", IMEM);
          $readmemh("srli_dmem.mem", DMEM);
        end
        `I_SRAI:
        begin
          $readmemh("srai_imem.mem", IMEM);
          $readmemh("srai_dmem.mem", DMEM);
        end

        // Conditional Branches [18:23]
        `B_BEQ:
        begin
          $readmemh("beq_imem.mem", IMEM);
          $readmemh("beq_dmem.mem", DMEM);
        end
        `B_BNE:
        begin
          $readmemh("bne_imem.mem", IMEM);
          $readmemh("bne_dmem.mem", DMEM);
        end
        `B_BLT:
        begin
          $readmemh("blt_imem.mem", IMEM);
          $readmemh("blt_dmem.mem", DMEM);
        end
        `B_BGE:
        begin
          $readmemh("bge_imem.mem", IMEM);
          $readmemh("bge_dmem.mem", DMEM);
        end
        `B_BLTU:
        begin
          $readmemh("bltu_imem.mem", IMEM);
          $readmemh("bltu_dmem.mem", DMEM);
        end
        `B_BGEU:
        begin
          $readmemh("bgeu_imem.mem", IMEM);
          $readmemh("bgeu_dmem.mem", DMEM);
        end

        // Upper Imm [24:25]
        `UI_LUI:
        begin
          $readmemh("lui_imem.mem", IMEM);
          $readmemh("lui_dmem.mem", DMEM);
        end
        `UI_AUIPC:
        begin
          $readmemh("auipc_imem.mem", IMEM);
          $readmemh("auipc_dmem.mem", DMEM);
        end

        // Jumps [26:27]
        `J_JAL:
        begin
          $readmemh("jal_imem.mem", IMEM);
          $readmemh("jal_dmem.mem", DMEM);
        end
        `J_JALR:
        begin
          $readmemh("jalr_imem.mem", IMEM);
          $readmemh("jalr_dmem.mem", DMEM);
        end

        // Loads [28:32]
        `L_LB:
        begin
          $readmemh("lb_imem.mem", IMEM);
          $readmemh("lb_dmem.mem", DMEM);
        end
        `L_LH:
        begin
          $readmemh("lh_imem.mem", IMEM);
          $readmemh("lh_dmem.mem", DMEM);
        end
        `L_LW:
        begin
          $readmemh("lw_imem.mem", IMEM);
          $readmemh("lw_dmem.mem", DMEM);
        end
        `L_LBU:
        begin
          $readmemh("lbu_imem.mem", IMEM);
          $readmemh("lbu_dmem.mem", DMEM);
        end
        `L_LHU:
        begin
          $readmemh("lhu_imem.mem", IMEM);
          $readmemh("lhu_dmem.mem", DMEM);
        end

        // Stores [33:35]
        `S_SB:
        begin
          $readmemh("sb_imem.mem", IMEM);
          $readmemh("sb_dmem.mem", DMEM);
        end
        `S_SH:
        begin
          $readmemh("sh_imem.mem", IMEM);
          $readmemh("sh_dmem.mem", DMEM);
        end
        `S_SW:
        begin
          $readmemh("sw_imem.mem", IMEM);
          $readmemh("sw_dmem.mem", DMEM);
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
