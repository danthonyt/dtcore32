module mem_stall_fsm (
    input logic CLK,
    output logic RST,
    output logic 
);
// disable dmem if address maps to axil peripheral
  
  always_ff @(posedge CLK) begin
    if (RST) begin
      axil_rdata_q <= 0;
      dmem_en_q <= 0;
      axil_done_read_q <= 0;
      axil_rmask_q <= 0;
    end else begin
      axil_rdata_q <= AXIL_TRANSACTION_RDATA;
      dmem_en_q <= dmem_en_d;
      axil_done_read_q <= AXIL_DONE_READ;
      axil_rmask_q <= axil_rmask_d;
    end
  end

  // select dmem write data OR axil write data OR neither
  always_comb begin
    mem_store_wdata_d = 0;
    mem_store_wmask_d = 0;
    if (dmem_en_d) begin
      mem_store_wdata_d = mem_dmem_wdata;
      mem_store_wmask_d = mem_dmem_wmask;
    end else if (axil_en_d) begin
      mem_store_wdata_d = AXIL_TRANSACTION_WRDATA;
      mem_store_wmask_d = 4'hf;
    end
  end

  // select dmem read data OR axil read data OR neither
  always_comb begin
    mem_load_rdata_d = 0;
    mem_load_rmask_d = 0;
    if (valid_axil_read) begin
      mem_load_rdata_d = AXIL_TRANSACTION_RDATA;
      mem_load_rmask_d = 4'hf;
    end else if (valid_dmem_read) begin
      mem_load_rdata_d = dmem_rdata_formatted;
      mem_load_rmask_d = dmem_rmask;
    end
  end

  assign axil_rmask_d = 4'hf;
  assign dmem_en_d = mem_pipeline.carried_trap.valid && dmem_en_comb;
  assign axil_en_d = mem_pipeline.carried_trap.valid && axil_en_comb;
  assign DMEM_EN = dmem_en_d;

  assign valid_axil_read = mem_pipeline.carried_trap.valid && axil_done_read_q;
  assign valid_dmem_read = mem_pipeline.carried_trap.valid && dmem_en_q;
endmodule