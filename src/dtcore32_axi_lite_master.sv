module dtcore32_axi_lite_master#(
    parameter BUS_WIDTH = 32
  )(
    // global signals
    input logic                           m_axi_aclk_i,
    input logic                           m_axi_aresetn_i,
    // read address channel
    output logic [31:0]                   m_axi_araddr_o,
    output logic [2:0]                    m_axi_arprot_o,
    output logic                          m_axi_arvalid_o,
    input  logic                          m_axi_arready_i,
    // read data channel
    input logic [BUS_WIDTH-1:0]           m_axi_rdata_i,
    input logic [1:0]                     m_axi_rresp_i,
    input logic                           m_axi_rvalid_i,
    output logic                           m_axi_rready_o,
    // write address channel
    output logic                          m_axi_awvalid_o,
    input  logic                          m_axi_awready_i,
    output logic [31:0]                   m_axi_awaddr_o,
    output logic [2:0]                    m_axi_awprot_o,
    // write data channel
    output logic                          m_axi_wvalid_o,
    input  logic                          m_axi_wready_i,
    output logic [BUS_WIDTH-1:0]           m_axi_wdata_o,
    output logic [(BUS_BYTE_WIDTH/8)-1:0]  m_axi_wstrb_o,
    // write response channel
    input  logic                          m_axi_bvalid_i,
    output logic                          m_axi_bready_o,
    input logic [1:0]                     m_axi_bresp_i,

    // Read FSM
    input logic start_read,
    input logic [31:0] raddr_i,
    output logic [BUS_WIDTH-1:0] rdata_o,
    output logic [1:0] rresp_msg_o,

    // Write FSM
    input logic start_write,
    input logic [31:0] wraddr_i,
    input logic [BUS_WIDTH-1:0] wrdata_i,
    output logic [1:0] bresp_msg_o,

  );

  ////////////////////////////////////////////////////////////////////////////////
  //
  //
  // WRITE FSM
  //
  //
  ////////////////////////////////////////////////////////////////////////////////

  // write address handshake
  always_ff (posedge m_axi_aclk_i, negedge m_axi_aresetn_i)
  begin
    if (!m_axi_aresetn_i)
    begin
      m_axi_wvalid_o <= 0;
      m_axi_wdata_o <= 0;
    end
    else if (start_write)
    begin
      m_axi_wvalid_o <= 1;
      m_axi_wdata_o <= wrdata_i;
    end
    else if (m_axi_wready_i & m_axi_wvalid_o)
    begin
      m_axi_wvalid_o <= 0;
      m_axi_wdata_o <= 0;
    end
  end

  // write data handshake
  always_ff (posedge m_axi_aclk_i, negedge m_axi_aresetn_i)
  begin
    if (!m_axi_aresetn_i)
    begin
      m_axi_awvalid_o <= 0;
      m_axi_awaddr_o <= 0;
    end
    else if (start_write)
    begin
      m_axi_awvalid_o <= 1;
      m_axi_awaddr_o <= wraddr_i;
    end
    else if (m_axi_awready_i & m_axi_awvalid_o)
    begin
      m_axi_awvalid_o <= 0;
      m_axi_awaddr_o <= 0;
    end
  end

  // write response handshake - the falling edge of bresp signals the end of the transaction
  // the write response can only happen after both the write address and write data handshake
  always_ff (posedge m_axi_aclk_i, negedge m_axi_aresetn_i)
  begin
    if (!m_axi_aresetn_i)
    begin
      bresp_msg_o <= 0;
      m_axi_bready_o <= 0;
    end
    else if (start_write)
    begin
      m_axi_bready_o <= 1;
    end
    else if ((m_axi_bvalid_i & m_axi_bready_o) & ~(m_axi_wready_i | m_axi_awready_i | m_axi_wvalid_o | m_axi_awvalid_o))
    begin
      m_axi_bready_o <= 0;
      bresp_msg_o <= m_axi_bresp_i;
    end
  end


  ////////////////////////////////////////////////////////////////////////////////
  //
  //
  // READ FSM
  //
  //
  ////////////////////////////////////////////////////////////////////////////////

  // read address handshake
  always_ff (posedge m_axi_aclk_i, negedge m_axi_aresetn_i)
  begin
    if (!m_axi_aresetn_i)
    begin
      m_axi_arvalid_o <= 0;
      m_axi_araddr_o <= 0;
      rdata_o <= 0;
    end
    else if (start_read)
    begin
      m_axi_arvalid_o <= 1;
      m_axi_araddr_o <= raddr_i;
    end
    else if (m_axi_arvalid_o & m_axi_arready_i)
    begin
      m_axi_arvalid_o <= 0;
      m_axi_araddr_o <= 0;
      rdata_o <= m_axi_rdata_i;
    end
  end

  // read response handshake
  always_ff (posedge m_axi_aclk_i, negedge m_axi_aresetn_i)
  begin
    if (!m_axi_aresetn_i)
    begin
      m_axi_rready_o <= 0;
      rresp_msg_o <= 0;
    end
    else if (start_read)
    begin
      m_axi_rready_o <= 1;
    end
    else if (~(m_axi_arvalid_o | m_axi_arready_i) & (m_axi_rvalid_i & m_axi_rready_o))
    begin
      m_axi_rready_o <= 0;
      rresp_msg_o <= m_axi_rresp_i;
    end
  end


  ////////////////////////////////////////////////////////////////////////////////
  //
  //
  // Formal Verification section begins here.
  //
  //
  ////////////////////////////////////////////////////////////////////////////////
`ifdef FORMAL
  // Concurrent properties are checked each *posedge* m_axi_aclk_i
  default clocking
            formal_clock @(posedge m_axi_aclk_i);
          endclocking

          // And disabled if the *m_axi_aresetn_i* reset is deasserted
          default disable iff (!m_axi_aresetn_i);
  // what do we need to test?
  // the AXI-lite specification will be used to decide this

  // In Figure A3-2, the source presents the address, data or control information after T1 and asserts the VALID signal.
  // "The destination asserts the READY signal after T2, and the source must keep its information stable until the transfer
  // occurs at T3, when this assertion is recognized."
stable_slave_in:
    assume property(m_axi_wvalid_o |-> $stable(m_axi_wdata_o))
      // "Once VALID is asserted it must remain asserted until the handshake occurs, at a rising clock edge at which VALID
      // and READY are both asserted." (A3.2.1)
  stable_valid:
        assert property(m_axi_wvalid_o |-> )
`endif
        endmodule

