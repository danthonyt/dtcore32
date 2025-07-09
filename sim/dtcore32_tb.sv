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


// Data Hazard tests
// Control Hazard tests

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

  typedef enum int {
    ADD,
    SUB,
    AND,
    OR,
    XOR,
    SLT,
    SLTU,
    SLL,
    SRL,
    SRA,
    ADDI,
    ANDI,
    ORI,
    XORI,
    SLTI,
    SLTIU,
    SLLI,
    SRLI,
    SRAI,
    BEQ,
    BNE,
    BLT,
    BGE,
    BLTU,
    BGEU,
    LUI,
    AUIPC,
    JAL,
    JALR,
    LB,
    LH,
    LW,
    LBU,
    LHU,
    SB,
    SH,
    SW,
    TESTID_NUM_TESTS
  } TESTID_t;

function string testid_to_string(TESTID_t id);
    case (id)
        ADD:    return "ADD";
        SUB:    return "SUB";
        AND:    return "AND";
        OR:     return "OR";
        XOR:    return "XOR";
        SLT:    return "SLT";
        SLTU:   return "SLTU";
        SLL:    return "SLL";
        SRL:    return "SRL";
        SRA:    return "SRA";
        ADDI:   return "ADDI";
        ANDI:   return "ANDI";
        ORI:    return "ORI";
        XORI:   return "XORI";
        SLTI:   return "SLTI";
        SLTIU:  return "SLTIU";
        SLLI:   return "SLLI";
        SRLI:   return "SRLI";
        SRAI:   return "SRAI";
        BEQ:    return "BEQ";
        BNE:    return "BNE";
        BLT:    return "BLT";
        BGE:    return "BGE";
        BLTU:   return "BLTU";
        BGEU:   return "BGEU";
        LUI:    return "LUI";
        AUIPC:  return "AUIPC";
        JAL:    return "JAL";
        JALR:   return "JALR";
        LB:     return "LB";
        LH:     return "LH";
        LW:     return "LW";
        LBU:    return "LBU";
        LHU:    return "LHU";
        SB:     return "SB";
        SH:     return "SH";
        SW:     return "SW";
        default: return "UNKNOWN_TEST";
    endcase
endfunction


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
    input TESTID_t TESTID;
    begin
      rst = 1;
      #10;
      for (i=0; i<= TESTID_NUM_TESTS; i=i+1)
      begin
        //MEMORY[i] = 0;
        DMEM[i] = 0;
        IMEM[i] = 0;
      end
      case(TESTID)

        // R-R [0:9]
        ADD:
        begin
          $readmemh("add_imem.mem", IMEM);
          $readmemh("add_dmem.mem", DMEM);
        end
        SUB:
        begin
          $readmemh("sub_imem.mem", IMEM);
          $readmemh("sub_dmem.mem", DMEM);
        end
        AND:
        begin
          $readmemh("and_imem.mem", IMEM);
          $readmemh("and_dmem.mem", DMEM);
        end
        OR:
        begin
          $readmemh("or_imem.mem", IMEM);
          $readmemh("or_dmem.mem", DMEM);
        end
        XOR:
        begin
          $readmemh("xor_imem.mem", IMEM);
          $readmemh("xor_dmem.mem", DMEM);
        end
        SLT:
        begin
          $readmemh("slt_imem.mem", IMEM);
          $readmemh("slt_dmem.mem", DMEM);
        end
        SLTU:
        begin
          $readmemh("sltu_imem.mem", IMEM);
          $readmemh("sltu_dmem.mem", DMEM);
        end
        SLL:
        begin
          $readmemh("sll_imem.mem", IMEM);
          $readmemh("sll_dmem.mem", DMEM);
        end
        SRL:
        begin
          $readmemh("srl_imem.mem", IMEM);
          $readmemh("srl_dmem.mem", DMEM);
        end
        SRA:
        begin
          $readmemh("sra_imem.mem", IMEM);
          $readmemh("sra_dmem.mem", DMEM);
        end

        // R-I [10:17]
        ADDI:
        begin
          $readmemh("addi_imem.mem", IMEM);
          $readmemh("addi_dmem.mem", DMEM);
        end
        ANDI:
        begin
          $readmemh("andi_imem.mem", IMEM);
          $readmemh("andi_dmem.mem", DMEM);
        end
        ORI:
        begin
          $readmemh("ori_imem.mem", IMEM);
          $readmemh("ori_dmem.mem", DMEM);
        end
        XORI:
        begin
          $readmemh("xori_imem.mem", IMEM);
          $readmemh("xori_dmem.mem", DMEM);
        end
        SLTI:
        begin
          $readmemh("slti_imem.mem", IMEM);
          $readmemh("slti_dmem.mem", DMEM);
        end
        SLTIU:
        begin
          $readmemh("sltiu_imem.mem", IMEM);
          $readmemh("sltiu_dmem.mem", DMEM);
        end
        SLLI:
        begin
          $readmemh("slli_imem.mem", IMEM);
          $readmemh("slli_dmem.mem", DMEM);
        end
        SRLI:
        begin
          $readmemh("srli_imem.mem", IMEM);
          $readmemh("srli_dmem.mem", DMEM);
        end
        SRAI:
        begin
          $readmemh("srai_imem.mem", IMEM);
          $readmemh("srai_dmem.mem", DMEM);
        end

        // Conditional Branches [18:23]
        BEQ:
        begin
          $readmemh("beq_imem.mem", IMEM);
          $readmemh("beq_dmem.mem", DMEM);
        end
        BNE:
        begin
          $readmemh("bne_imem.mem", IMEM);
          $readmemh("bne_dmem.mem", DMEM);
        end
        BLT:
        begin
          $readmemh("blt_imem.mem", IMEM);
          $readmemh("blt_dmem.mem", DMEM);
        end
        BGE:
        begin
          $readmemh("bge_imem.mem", IMEM);
          $readmemh("bge_dmem.mem", DMEM);
        end
        BLTU:
        begin
          $readmemh("bltu_imem.mem", IMEM);
          $readmemh("bltu_dmem.mem", DMEM);
        end
        BGEU:
        begin
          $readmemh("bgeu_imem.mem", IMEM);
          $readmemh("bgeu_dmem.mem", DMEM);
        end

        // Upper Imm [24:25]
        LUI:
        begin
          $readmemh("lui_imem.mem", IMEM);
          $readmemh("lui_dmem.mem", DMEM);
        end
        AUIPC:
        begin
          $readmemh("auipc_imem.mem", IMEM);
          $readmemh("auipc_dmem.mem", DMEM);
        end

        // Jumps [26:27]
        JAL:
        begin
          $readmemh("jal_imem.mem", IMEM);
          $readmemh("jal_dmem.mem", DMEM);
        end
        JALR:
        begin
          $readmemh("jalr_imem.mem", IMEM);
          $readmemh("jalr_dmem.mem", DMEM);
        end

        // Loads [28:32]
        LB:
        begin
          $readmemh("lb_imem.mem", IMEM);
          $readmemh("lb_dmem.mem", DMEM);
        end
        LH:
        begin
          $readmemh("lh_imem.mem", IMEM);
          $readmemh("lh_dmem.mem", DMEM);
        end
        LW:
        begin
          $readmemh("lw_imem.mem", IMEM);
          $readmemh("lw_dmem.mem", DMEM);
        end
        LBU:
        begin
          $readmemh("lbu_imem.mem", IMEM);
          $readmemh("lbu_dmem.mem", DMEM);
        end
        LHU:
        begin
          $readmemh("lhu_imem.mem", IMEM);
          $readmemh("lhu_dmem.mem", DMEM);
        end

        // Stores [33:35]
        SB:
        begin
          $readmemh("sb_imem.mem", IMEM);
          $readmemh("sb_dmem.mem", DMEM);
        end
        SH:
        begin
          $readmemh("sh_imem.mem", IMEM);
          $readmemh("sh_dmem.mem", DMEM);
        end
        SW:
        begin
          $readmemh("sw_imem.mem", IMEM);
          $readmemh("sw_dmem.mem", DMEM);
        end


      endcase
    end
  endtask // LOAD_TEST



  integer t;
  task EVAL_TEST;
    input TESTID_t TESTID;
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
             $display("TEST PASSED; ID: %s", testid_to_string(TESTID));
             t=1000000;

           end
           else if (Exception == 1)
           begin
             $display("EXCEPTION ASSERTED, TEST FAILED");
             $display("FAILED TEST ID: %s", testid_to_string(TESTID));
             $finish;

           end
           else if (t==999999)
           begin
             $display("TEST FAILED: TIMED OUT");
             $display("FAILED TEST ID: %s", testid_to_string(TESTID));
             $display("FAILED TEST CASE: %0d", UUT.dtcore32_ID_stage_inst.dtcore32_regfile_inst.reg_array[11]);
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
    begin
      $display("Running all tests.");
      for(j=0; j<=TESTID_NUM_TESTS; j=j+1)
      begin
        $display("***********************************");
        $display("Running Test ID: %s", testid_to_string(TESTID_t'(j)));
        LOAD_TEST(j);
        #100;
        EVAL_TEST(j);

      end
      $display("");
      $display("***********************************");
      $display("ALL TESTS PASSED !");
      $finish;

    end
  end
endmodule
