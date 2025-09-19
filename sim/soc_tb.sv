`define RISCV_FORMAL
module soc_tb ();
  logic clk = 0;
  logic rst;
  logic led_trap;
  logic tx;


  always #5ns clk = ~clk;

  soc_top soc_top_inst (
      .clk_i(clk),
      .rst_i(rst),
      .led_trap(led_trap),
      .tx_o (tx)
  );
  localparam IMEM_BASE_ADDR = 0;
  localparam IMEM_LENGTH = 16384;
  localparam DMEM_BASE_ADDR = 32'h0010_0000;
  localparam DMEM_LENGTH = 16384;
  localparam UART_BASE_ADDR = 32'h0100_0000;
  localparam UART_LENGTH = 16;
  logic [31:0] mem_addr;
  logic [31:0] id_insn;
  logic [31:0] ex_insn;
  logic [31:0] mem_insn;
  logic [31:0] wb_insn;
  logic [31:0] id_pc;
  logic [31:0] ex_pc;
  logic [31:0] mem_pc;
  logic [31:0] wb_pc;

  assign id_insn = soc_top_inst.dtcore32_inst.id_pipeline_q.insn;
  assign ex_insn = soc_top_inst.dtcore32_inst.ex_pipeline_q.insn;
  assign mem_insn = soc_top_inst.dtcore32_inst.mem_pipeline_q.insn;
  assign wb_insn = soc_top_inst.dtcore32_inst.wb_pipeline_q.insn;
  assign id_pc = soc_top_inst.dtcore32_inst.id_pipeline_q.pc;
  assign ex_pc = soc_top_inst.dtcore32_inst.ex_pipeline_q.pc;
  assign mem_pc = soc_top_inst.dtcore32_inst.mem_pipeline_q.pc;
  assign wb_pc = soc_top_inst.dtcore32_inst.wb_pipeline_q.pc;
  assign mem_addr = soc_top_inst.mem_addr;

  always @(posedge clk) begin
    if (1) begin
      if (soc_top_inst.dtcore32_inst.dmem_periph_req && soc_top_inst.dtcore32_inst.mem_valid_o) begin
        if ((mem_addr >= IMEM_BASE_ADDR) && (mem_addr < (IMEM_BASE_ADDR + IMEM_LENGTH * 4))) begin
          $error("MEM stage tried to access IMEM -- PC: %h ADDR: %h",
                 soc_top_inst.dtcore32_inst.mem_pipeline_q.pc,
                 soc_top_inst.dtcore32_inst.mem_pipeline_q.alu_csr_result);
          $finish();
        end else if ((mem_addr >= DMEM_BASE_ADDR) && (mem_addr < (DMEM_BASE_ADDR + DMEM_LENGTH*4))) begin
          if (soc_top_inst.dtcore32_inst.wb_pipeline_q.load_rmask)
            $display(
                " DMEM LOAD --- PC: %h, ADDR: %h, LOAD_RMASK: %h, LOAD_RDATA: %h",
                soc_top_inst.dtcore32_inst.wb_pipeline_q.pc,
                soc_top_inst.dtcore32_inst.wb_pipeline_q.mem_addr,
                soc_top_inst.dtcore32_inst.wb_pipeline_q.load_rmask,
                soc_top_inst.dtcore32_inst.wb_pipeline_q.load_rdata,
            );
          else if (soc_top_inst.dtcore32_inst.wb_pipeline_q.store_wmask)
            $display(
                "DMEM STORE --- PC: %h, ADDR: %h, STORE_WMASK: %h, STORE_WDATA: %h",
                soc_top_inst.dtcore32_inst.wb_pipeline_q.pc,
                soc_top_inst.dtcore32_inst.wb_pipeline_q.mem_addr,
                soc_top_inst.dtcore32_inst.wb_pipeline_q.store_wmask,
                soc_top_inst.dtcore32_inst.wb_pipeline_q.store_wdata,
            );
        end else if (mem_addr >= UART_BASE_ADDR && mem_addr < UART_BASE_ADDR + UART_LENGTH) begin
          if (soc_top_inst.dtcore32_inst.wb_pipeline_q.load_rmask)
            $display(
                " UART LOAD --- PC: %h, ADDR: %h, LOAD_RMASK: %h, LOAD_RDATA: %h",
                soc_top_inst.dtcore32_inst.wb_pipeline_q.pc,
                soc_top_inst.dtcore32_inst.wb_pipeline_q.mem_addr,
                soc_top_inst.dtcore32_inst.wb_pipeline_q.load_rmask,
                soc_top_inst.dtcore32_inst.wb_pipeline_q.load_rdata,
            );
          else if (soc_top_inst.dtcore32_inst.wb_pipeline_q.store_wmask)
            $display(
                "UART STORE --- PC: %h, ADDR: %h, STORE_WMASK: %h, STORE_WDATA: %h",
                soc_top_inst.dtcore32_inst.wb_pipeline_q.pc,
                soc_top_inst.dtcore32_inst.wb_pipeline_q.mem_addr,
                soc_top_inst.dtcore32_inst.wb_pipeline_q.store_wmask,
                soc_top_inst.dtcore32_inst.wb_pipeline_q.store_wdata,
            );

        end else begin
          $error("MEM stage tried to access UNKNOWN PERIPHERAL -- ADR: %h PC: %h",
                 soc_top_inst.dtcore32_inst.mem_pipeline_q.alu_csr_result,
                 soc_top_inst.dtcore32_inst.mem_pipeline_q.pc);
          $finish();
        end
      end
    end
  end



  // RISC-V register names
  string reg_names[0:31] = '{
      "zero",
      "ra",
      "sp",
      "gp",
      "tp",
      "t0",
      "t1",
      "t2",
      "s0",
      "s1",
      "a0",
      "a1",
      "a2",
      "a3",
      "a4",
      "a5",
      "a6",
      "a7",
      "s2",
      "s3",
      "s4",
      "s5",
      "s6",
      "s7",
      "s8",
      "s9",
      "s10",
      "s11",
      "t3",
      "t4",
      "t5",
      "t6"
  };

  reg [31:0] regfile_shadow[0:31];
  integer i;

  always @(posedge clk) begin
    if (0) begin
      for (i = 0; i < 32; i = i + 1) begin
        if (soc_top_inst.dtcore32_inst.regfile_inst.reg_array[i] !== regfile_shadow[i]) begin
          $display("Time %0t: PC=0x%08h | %s changed from 0x%08h to 0x%08h", $time, pc_delay,
                   reg_names[i], regfile_shadow[i],
                   soc_top_inst.dtcore32_inst.regfile_inst.reg_array[i]);
          // update shadow
          regfile_shadow[i] <= soc_top_inst.dtcore32_inst.regfile_inst.reg_array[i];
        end
      end
    end
  end

  // instructions retired
always @(negedge clk) begin
    if (1) begin
        if (!soc_top_inst.dtcore32_inst.mem_wb_stall && soc_top_inst.dtcore32_inst.wb_pipeline_q.valid) begin
            $display(
                "Time %0t: Retired instruction: %h, PC: %h",
                $time,
                soc_top_inst.dtcore32_inst.wb_pipeline_q.insn,
                soc_top_inst.dtcore32_inst.wb_pipeline_q.pc
            );
        end
    end
end


  logic [31:0] pc_delay;
  logic [31:0] instr_delay;

  always @(posedge clk) begin
    pc_delay <= soc_top_inst.dtcore32_inst.wb_pipeline_q.pc;
    instr_delay <= soc_top_inst.dtcore32_inst.wb_pipeline_q.insn;
  end

  reg [31:0] dmem_shadow[0:DMEM_LENGTH-1];
  integer j;

  always @(posedge clk) begin
    if (0) begin
      for (j = 0; j < DMEM_LENGTH; j = j + 1) begin
        if (soc_top_inst.dmem_inst.MEM[j] !== dmem_shadow[j]) begin
          $display("Time %0t: PC=0x%08h | DMEM[%d] changed from 0x%08h to 0x%08h", $time,
                   soc_top_inst.dtcore32_inst.mem_pipeline_q.pc, j, dmem_shadow[j],
                   soc_top_inst.dmem_inst.MEM[j]);
          // update shadow
          dmem_shadow[j] <= soc_top_inst.dmem_inst.MEM[j];
        end
      end
    end
  end




  parameter CLK_PERIOD = 10;  // adjust to your simulation clock period
  parameter BIT_PERIOD = 8680; // adjust to match baud rate (example for 115200 baud at 100MHz clock)


  // reset
  initial begin
    rst = 1;
    #20 rst = 0;
  end

  /*
  // --- send a character via RX ---
  task uart_send_byte(input [7:0] data);
    integer i;
    begin
      // start bit
      rx = 0;
      #(BIT_PERIOD);

      // send 8 data bits, LSB first
      for (i = 0; i < 8; i = i + 1) begin
        rx = data[i];
        #(BIT_PERIOD);
      end

      // stop bit
      rx = 1;
      #(BIT_PERIOD);
    end
  endtask
    */

  // --- main test sequence ---
  initial begin
    @(negedge rst);  // wait for reset deassertion
    #5s;
    // send "A" (0x41)
    //uart_send_byte(8'h41);

    // send "B" (0x42)
    //uart_send_byte(8'h42);
    #1000us;
    //wait(soc_top_inst.dtcore32_inst.wb_pipeline_q.valid && soc_top_inst.dtcore32_inst.wb_pipeline_q.pc == 32'h2d54)
    // wait some time and finish simulation
    $finish;
  end
endmodule
