module soc_tb ();
  logic clk = 0;
  logic rst;
  logic rx;
  logic tx;

  always #5 clk = ~clk;

  soc_top soc_top_inst (
      .CLK_I(clk),
      .RST_I(rst),
      .RX_I (rx),
      .TX_O (tx)
  );
  localparam IMEM_BASE_ADDR = 0;
  localparam IMEM_LENGTH = 1024;
  localparam DMEM_BASE_ADDR = 32'h0010_0000;
  localparam DMEM_LENGTH = 1024;
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

  assign id_insn = soc_top_inst.dtcore32_inst.id_pipeline.insn;
  assign ex_insn = soc_top_inst.dtcore32_inst.ex_pipeline.insn;
  assign mem_insn = soc_top_inst.dtcore32_inst.mem_pipeline.insn;
  assign wb_insn = soc_top_inst.dtcore32_inst.wb_pipeline.insn;
  assign id_pc = soc_top_inst.dtcore32_inst.id_pipeline.pc;
  assign ex_pc = soc_top_inst.dtcore32_inst.ex_pipeline.pc;
  assign mem_pc = soc_top_inst.dtcore32_inst.mem_pipeline.pc;
  assign wb_pc = soc_top_inst.dtcore32_inst.wb_pipeline.pc;
  assign mem_addr = soc_top_inst.CPU_MEM_CMD_ADDR_I;

  always @(posedge clk) begin
    if (soc_top_inst.dtcore32_inst.wb_pipeline.load_rmask) 
        $display(" LOAD --- PC: %h, ADDR: %h, LOAD_RMASK: %h, LOAD_RDATA: %h",
        soc_top_inst.dtcore32_inst.wb_pipeline.pc,
        soc_top_inst.dtcore32_inst.wb_pipeline.alu_csr_result,
        soc_top_inst.dtcore32_inst.wb_pipeline.load_rmask,
        soc_top_inst.dtcore32_inst.wb_pipeline.load_rdata,
        );
        else if(soc_top_inst.dtcore32_inst.wb_pipeline.store_wmask) 
        $display("STORE --- PC: %h, ADDR: %h, STORE_WMASK: %h, STORE_WDATA: %h",
        soc_top_inst.dtcore32_inst.wb_pipeline.pc,
        soc_top_inst.dtcore32_inst.wb_pipeline.alu_csr_result,
        soc_top_inst.dtcore32_inst.wb_pipeline.store_wmask,
        soc_top_inst.dtcore32_inst.wb_pipeline.store_wdata,
        );
    if (soc_top_inst.dtcore32_inst.mem_cmd_req) begin
      if (mem_addr >= IMEM_BASE_ADDR && mem_addr < IMEM_BASE_ADDR + IMEM_LENGTH) begin
        $error("MEM stage tried to access IMEM -- PC: %h",
        soc_top_inst.dtcore32_inst.mem_pipeline.pc);
        $finish();
      end else if (mem_addr >= DMEM_BASE_ADDR && mem_addr < DMEM_BASE_ADDR + DMEM_LENGTH) begin
        if (soc_top_inst.dtcore32_inst.wb_pipeline.load_rmask) 
        $display(" LOAD --- PC: %h, ADDR: %h, LOAD_RMASK: %h, LOAD_RDATA: %h",
        soc_top_inst.dtcore32_inst.wb_pipeline.pc,
        soc_top_inst.dtcore32_inst.wb_pipeline.alu_csr_result,
        soc_top_inst.dtcore32_inst.wb_pipeline.load_rmask,
        soc_top_inst.dtcore32_inst.wb_pipeline.load_rdata,
        );
        else if(soc_top_inst.dtcore32_inst.wb_pipeline.store_wmask) 
        $display("STORE --- PC: %h, ADDR: %h, STORE_WMASK: %h, STORE_WDATA: %h",
        soc_top_inst.dtcore32_inst.wb_pipeline.pc,
        soc_top_inst.dtcore32_inst.wb_pipeline.alu_csr_result,
        soc_top_inst.dtcore32_inst.wb_pipeline.store_wmask,
        soc_top_inst.dtcore32_inst.wb_pipeline.store_wdata,
        );
      end else if (mem_addr >= UART_BASE_ADDR && mem_addr < UART_BASE_ADDR + UART_LENGTH) begin
        if (soc_top_inst.dtcore32_inst.wb_pipeline.load_rmask) 
        $display(" UART LOAD --- PC: %h, ADDR: %h, LOAD_RMASK: %h, LOAD_RDATA: %h",
        soc_top_inst.dtcore32_inst.wb_pipeline.pc,
        soc_top_inst.dtcore32_inst.wb_pipeline.alu_csr_result,
        soc_top_inst.dtcore32_inst.wb_pipeline.load_rmask,
        soc_top_inst.dtcore32_inst.wb_pipeline.load_rdata,
        );
        else if(soc_top_inst.dtcore32_inst.wb_pipeline.store_wmask) 
        $display("UART STORE --- PC: %h, ADDR: %h, STORE_WMASK: %h, STORE_WDATA: %h",
        soc_top_inst.dtcore32_inst.wb_pipeline.pc,
        soc_top_inst.dtcore32_inst.wb_pipeline.alu_csr_result,
        soc_top_inst.dtcore32_inst.wb_pipeline.store_wmask,
        soc_top_inst.dtcore32_inst.wb_pipeline.store_wdata,
        );

      end else begin
        $error("MEM stage tried to access UNKNOWN PERIPHERAL -- PC: %h",
        soc_top_inst.dtcore32_inst.mem_pipeline.pc);
        $finish();
      end
    end
  end


// RISC-V register names
string reg_names[0:31] = '{
    "zero","ra","sp","gp","tp",
    "t0","t1","t2","s0","s1",
    "a0","a1","a2","a3","a4","a5","a6","a7",
    "s2","s3","s4","s5","s6","s7","s8","s9","s10","s11",
    "t3","t4","t5","t6"
};

reg [31:0] regfile_shadow[0:31];
integer i;

always @(posedge clk) begin
    for (i = 0; i < 32; i = i + 1) begin
        if (soc_top_inst.dtcore32_inst.regfile_inst.reg_array[i] !== regfile_shadow[i]) begin
            $display("Time %0t: PC=0x%08h | %s changed from 0x%08h to 0x%08h",
                     $time,
                     pc_delay,
                     reg_names[i],
                     regfile_shadow[i],
                     soc_top_inst.dtcore32_inst.regfile_inst.reg_array[i]);
            // update shadow
            regfile_shadow[i] <= soc_top_inst.dtcore32_inst.regfile_inst.reg_array[i];
        end
    end
end

logic [31:0] pc_delay;

always @(posedge clk) begin
    pc_delay <= soc_top_inst.dtcore32_inst.wb_pipeline.pc;
end


// Assume 1 KB DMEM
localparam DMEM_SIZE = 1024;
reg [31:0] dmem_shadow [0:DMEM_SIZE-1];
integer j;

always @(posedge clk) begin
    for (j = 0; j < DMEM_SIZE; j = j + 1) begin
        if (soc_top_inst.wb_ram_inst.MEM[j] !== dmem_shadow[j]) begin
            $display("Time %0t: PC=0x%08h | DMEM[0x%03h] changed from 0x%08h to 0x%08h",
                     $time,
                     soc_top_inst.dtcore32_inst.mem_pipeline.pc,
                     j,
                     dmem_shadow[j],
                     soc_top_inst.wb_ram_inst.MEM[j]);
            // update shadow
            dmem_shadow[j] <= soc_top_inst.wb_ram_inst.MEM[j];
        end
    end
end



  initial begin
    rst = 1;
    #20 rst = 0;

    // optional: run simulation for some cycles
    #4us $finish;
  end
endmodule
