
module soc_tb ();
  logic clk = 0;
  logic rst;
  logic tx;


  always #5ns clk = ~clk;

  soc_top soc_top_inst (
      .clk_i(clk),
      .rst_i(rst),
      .tx_o(tx)
  );
  // byte addressable memory; 
  // 1 address, 1 byte
  localparam IMEM_BASE_ADDR = 0;
  localparam IMEM_LENGTH = 20'h10000;
  localparam DMEM_BASE_ADDR = 32'h0010_0000;
  localparam DMEM_LENGTH = 20'h10000;
  localparam UART_BASE_ADDR = 32'h0100_0000;
  localparam UART_LENGTH = 8'h10;
  logic [31:0] mem_addr;
  logic [31:0] id_insn;
  logic [31:0] ex_insn;
  logic [31:0] mem_insn;
  logic [31:0] wb_insn;
  logic [31:0] id_pc;
  logic [31:0] ex_pc;
  logic [31:0] mem_pc;
  logic [31:0] wb_pc;
  logic uart_req;
  logic dmem_req;
  logic imem_req;
  logic valid_req;
  logic [3:0] mem_rmask;
  logic [3:0] mem_wmask;
  assign mem_rmask = soc_top_inst.dtcore32_inst.mem_rstrb;
  assign mem_wmask = soc_top_inst.dtcore32_inst.mem_wstrb;

  assign id_insn = soc_top_inst.dtcore32_inst.id_q_insn;
  assign ex_insn = soc_top_inst.dtcore32_inst.ex_q_insn;
  assign mem_insn = soc_top_inst.dtcore32_inst.mem_q_insn;
  assign wb_insn = soc_top_inst.dtcore32_inst.wb_q_insn;
  assign id_pc = soc_top_inst.dtcore32_inst.id_q_pc;
  assign ex_pc = soc_top_inst.dtcore32_inst.ex_q_pc;
  assign mem_pc = soc_top_inst.dtcore32_inst.mem_q_pc;
  assign wb_pc = soc_top_inst.dtcore32_inst.wb_q_pc;
  assign mem_addr = soc_top_inst.mem_addr;

  assign valid_req = soc_top_inst.mem_done;
  assign uart_req = (mem_addr >= UART_BASE_ADDR) && (mem_addr < (UART_BASE_ADDR + UART_LENGTH));
  assign dmem_req = (mem_addr >= DMEM_BASE_ADDR) && (mem_addr < (DMEM_BASE_ADDR + DMEM_LENGTH));
  assign imem_req = (mem_addr >= IMEM_BASE_ADDR) && (mem_addr < (IMEM_BASE_ADDR + IMEM_LENGTH));
  always @(posedge clk) begin
    if (1) begin
      if (valid_req) begin
        if (imem_req) begin
          if (soc_top_inst.dtcore32_inst.mem_d_store_wmask) begin
            $error("MEM stage tried to write to IMEM -- PC: %h ADDR: %h",
                   soc_top_inst.dtcore32_inst.mem_d_pc,
                   soc_top_inst.dtcore32_inst.mem_d_mem_addr);
            $finish();
          end else begin
            $display(
                "%s --- PC: %h, ADDR: %h, LOAD_RMASK: %h, LOAD_RDATA: %h, STORE_WMASK: %h, STORE_WDATA: %h",
                soc_top_inst.dtcore32_inst.mem_d_load_rmask ? "IMEM LOAD" : "UNKNOWN IMEM REQ",
                soc_top_inst.dtcore32_inst.mem_d_pc,
                soc_top_inst.dtcore32_inst.mem_d_mem_addr,
                soc_top_inst.dtcore32_inst.mem_d_load_rmask,
                soc_top_inst.dtcore32_inst.mem_d_load_rdata,
                soc_top_inst.dtcore32_inst.mem_d_store_wmask,
                soc_top_inst.dtcore32_inst.mem_d_store_wdata);
          end

        end else if (dmem_req) begin
          $display(
              "%s --- PC: %h, ADDR: %h, LOAD_RMASK: %h, LOAD_RDATA: %h, STORE_WMASK: %h, STORE_WDATA: %h",
              soc_top_inst.dtcore32_inst.mem_d_load_rmask ? "DMEM LOAD" : (soc_top_inst.dtcore32_inst.mem_d_store_wmask ? "DMEM STORE" : "UNKNOWN DMEM REQ"),
              soc_top_inst.dtcore32_inst.mem_d_pc,
              soc_top_inst.dtcore32_inst.mem_d_mem_addr,
              soc_top_inst.dtcore32_inst.mem_d_load_rmask,
              soc_top_inst.dtcore32_inst.mem_d_load_rdata,
              soc_top_inst.dtcore32_inst.mem_d_store_wmask,
              soc_top_inst.dtcore32_inst.mem_d_store_wdata);

        end else if (uart_req) begin
          $display(
              "%s --- PC: %h, ADDR: %h, LOAD_RMASK: %h, LOAD_RDATA: %h, STORE_WMASK: %h, STORE_WDATA: %h",
              soc_top_inst.dtcore32_inst.mem_d_load_rmask ? "UART LOAD" : (soc_top_inst.dtcore32_inst.mem_d_store_wmask ? "UART STORE" : "UNKNOWN UART REQ"),
              soc_top_inst.dtcore32_inst.mem_d_pc,
              soc_top_inst.dtcore32_inst.mem_d_mem_addr,
              soc_top_inst.dtcore32_inst.mem_d_load_rmask,
              soc_top_inst.dtcore32_inst.mem_d_load_rdata,
              soc_top_inst.dtcore32_inst.mem_d_store_wmask,
              soc_top_inst.dtcore32_inst.mem_d_store_wdata);
        end else begin
          $error("MEM stage tried to access UNKNOWN PERIPHERAL -- ADR: %h PC: %h",
                 soc_top_inst.dtcore32_inst.mem_d_mem_addr,
                 soc_top_inst.dtcore32_inst.mem_d_pc);
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
        if (soc_top_inst.dtcore32_inst.regfile_arr[i] !== regfile_shadow[i]) begin
          $display("Time %0t: PC=0x%08h | %s changed from 0x%08h to 0x%08h", $time, pc_delay,
                   reg_names[i], regfile_shadow[i],
                   soc_top_inst.dtcore32_inst.regfile_arr[i]);
          // update shadow
          regfile_shadow[i] <= soc_top_inst.dtcore32_inst.regfile_arr[i];
        end
      end
    end
  end

  // instructions retired
  always @(negedge clk) begin
    if (0) begin
      if (!soc_top_inst.dtcore32_inst.mem_wb_stall && soc_top_inst.dtcore32_inst.wb_q_valid) begin
        $display("Time %0t: Retired instruction: %h, PC: %h", $time,
                 soc_top_inst.dtcore32_inst.wb_q_insn,
                 soc_top_inst.dtcore32_inst.wb_q_pc);
      end
    end
  end


  logic [31:0] pc_delay;
  logic [31:0] instr_delay;

  always @(posedge clk) begin
    pc_delay <= soc_top_inst.dtcore32_inst.wb_q_pc;
    instr_delay <= soc_top_inst.dtcore32_inst.wb_q_insn;
  end

  reg [31:0] dmem_shadow[0:DMEM_LENGTH-1];
  integer j;

  always @(posedge clk) begin
    if (0) begin
      for (j = 0; j < DMEM_LENGTH; j = j + 1) begin
        if (soc_top_inst.dmem_inst.MEM[j] !== dmem_shadow[j]) begin
          $display("Time %0t: PC=0x%08h | DMEM[%d] changed from 0x%08h to 0x%08h", $time,
                   soc_top_inst.dtcore32_inst.mem_q_pc, j, dmem_shadow[j],
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
    // send "A" (0x41)
    //uart_send_byte(8'h41);

    // send "B" (0x42)
    //uart_send_byte(8'h42);
    #3ms;
    //wait(soc_top_inst.dtcore32_inst.wb_q_valid && soc_top_inst.dtcore32_inst.wb_q_pc == 32'h2d54)
    // wait some time and finish simulation
    $finish;
  end
endmodule
