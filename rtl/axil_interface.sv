// this module starts an axil transaction if 
// the address is an axil address, AND the instruction is a LW or SW,
// 

module axil_interface
  import params_pkg::*;
#(
    ADDR_WIDTH = 32,
    BUS_WIDTH = 32,
    ENABLE_WRITE = 1
) (
    input  logic                        CLK,
    input  logic                        RST,
    input  logic                        EN,
    input  mem_op_t                     MEM_OP,
    input  logic    [             31:0] MEM_WDATA,
    input  logic    [             3:0] MEM_WSTRB,
    input  logic    [   ADDR_WIDTH-1:0] AXIL_ADDR,
    // axil
    input  logic                        AXIL_DONE_READ,
    input  logic                        AXIL_DONE_WRITE,
    input  logic    [    BUS_WIDTH-1:0] AXIL_TRANSACTION_RDATA,
    output logic                        AXIL_START_READ,
    output logic                        AXIL_START_WRITE,
    output logic    [   ADDR_WIDTH-1:0] AXIL_TRANSACTION_WRADDR,
    output logic    [    BUS_WIDTH-1:0] AXIL_TRANSACTION_WRDATA,
    output logic    [(BUS_WIDTH/8)-1:0] AXIL_TRANSACTION_WSTRB,
    output logic    [   ADDR_WIDTH-1:0] AXIL_TRANSACTION_RADDR
);


  logic axil_rreq_pending;
  logic axil_rreq;
  logic axil_wreq_pending;
  logic axil_wreq;

  // generate a single clock pulse for a new read request
  always_ff @(posedge CLK) begin
    if (RST) begin
      axil_rreq_pending <= 0;
    end else if (AXIL_DONE_READ) begin
      // Transaction finished, clear pending
      axil_rreq_pending <= 0;
    end else if (axil_rreq && !axil_rreq_pending) begin
      // New memory request, latch pending
      axil_rreq_pending <= 1;
    end
  end

  always_comb begin
    if (EN) begin
      axil_rreq = (MEM_OP == MEM_LW);
      AXIL_START_READ = axil_rreq && !axil_rreq_pending;
      AXIL_TRANSACTION_RADDR = AXIL_ADDR;
    end else begin
      axil_rreq = 0;
      AXIL_TRANSACTION_RADDR = 0;
      AXIL_START_READ = 0;
    end
  end

  generate
    if (ENABLE_WRITE) begin

      always_comb begin
        if (EN) begin
          axil_wreq = (MEM_OP == MEM_SW);
          AXIL_START_WRITE = axil_wreq && !axil_wreq_pending;
          AXIL_TRANSACTION_WRADDR = AXIL_ADDR;
          AXIL_TRANSACTION_WSTRB = MEM_WSTRB;
          AXIL_TRANSACTION_WRDATA = MEM_WDATA;
        end else begin
          axil_wreq = 0;
          AXIL_START_WRITE = 0;
          AXIL_TRANSACTION_WRADDR = 0;
          AXIL_TRANSACTION_WSTRB = 0;
          AXIL_TRANSACTION_WRDATA = 0;
        end
      end

      // generate a single clock pulse for a new write request
      always_ff @(posedge CLK) begin
        if (RST) begin
          axil_wreq_pending <= 0;
        end else if (AXIL_DONE_WRITE) begin
          // Transaction finished, clear pending
          axil_wreq_pending <= 0;
        end else if (axil_wreq && !axil_wreq_pending) begin
          // New memory request, latch pending
          axil_wreq_pending <= 1;
        end
      end
    end
  endgenerate

endmodule
