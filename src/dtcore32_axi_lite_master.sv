module dtcore32_axi_lite_master#(
    parameter int BUS_WIDTH = 32
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
    output logic [(BUS_WIDTH/8)-1:0]  m_axi_wstrb_o,
    // write response channel
    input  logic                          m_axi_bvalid_i,
    output logic                          m_axi_bready_o,
    input logic [1:0]                     m_axi_bresp_i,

    // Read 
    input logic start_read_i,
    input logic [31:0] raddr_i,
    output logic [BUS_WIDTH-1:0] rdata_o,
    output logic [1:0] rresp_msg_o,

    // Write 
    input logic start_write_i,
    input logic [31:0] wraddr_i,
    input logic [BUS_WIDTH-1:0] wrdata_i,
    output logic [1:0] bresp_msg_o
  );
  logic [31:0]                   m_axi_araddr_int;
  logic [2:0]                    m_axi_arprot_int;
  logic                          m_axi_arvalid_int;
  logic                           m_axi_rready_int;
  logic                          m_axi_awvalid_int;
  logic [31:0]                   m_axi_awaddr_int;
  logic [2:0]                    m_axi_awprot_int;
  logic                          m_axi_wvalid_int;
  logic [BUS_WIDTH-1:0]           m_axi_wdata_int;
  logic [(BUS_WIDTH/8)-1:0]  m_axi_wstrb_int;
  logic                          m_axi_bready_int;
  logic [BUS_WIDTH-1:0] rdata_int;
  logic [1:0] rresp_msg_int;
  logic [1:0] bresp_msg_int;
  logic [31:0] raddr_reg;
  logic [31:0] wraddr_reg;

  // write data handshake
  always_ff @(posedge m_axi_aclk_i, negedge m_axi_aresetn_i)
  begin
    if (!m_axi_aresetn_i)
    begin
      m_axi_wvalid_int <= 0;
      m_axi_wdata_int <= 0;
    end
    else if (start_write_i & ~m_axi_wvalid_int)
    begin
      m_axi_wvalid_int <= 1;
      m_axi_wdata_int <= wrdata_i;
    end
    else if (m_axi_wready_i & m_axi_wvalid_int)
    begin
      m_axi_wvalid_int <= 0;
      m_axi_wdata_int <= 0;
    end
  end

  // write address handshake
  always_ff @(posedge m_axi_aclk_i, negedge m_axi_aresetn_i)
  begin
    if (!m_axi_aresetn_i)
    begin
      wraddr_reg <= 0;
      m_axi_awvalid_int <= 0;
      m_axi_awaddr_int <= 0;
      m_axi_wstrb_int <= 0;
    end
    else if (start_write_i & ~m_axi_awvalid_int)
    begin
      wraddr_reg <= wraddr_i;
      m_axi_awvalid_int <= 1;
      m_axi_awaddr_int <= wraddr_reg;
      m_axi_wstrb_int <= 8'hff;
    end
    else if (m_axi_awready_i & m_axi_awvalid_int)
    begin
      wraddr_reg <= 0;
      m_axi_awvalid_int <= 0;
      m_axi_awaddr_int <= 0;
    end
  end

  // write response handshake - the falling edge of bresp signals the end of the transaction
  // the write response can only happen after both the write address and write data handshake
  always_ff @(posedge m_axi_aclk_i, negedge m_axi_aresetn_i)
  begin
    if (!m_axi_aresetn_i)
    begin
      bresp_msg_int <= 0;
      m_axi_bready_int <= 0;
    end
    else if (start_write_i & ~m_axi_bready_int)
    begin
      m_axi_bready_int <= 1;
    end
    else if ((m_axi_bvalid_i & m_axi_bready_int) & ~(m_axi_wready_i | m_axi_awready_i | m_axi_wvalid_int | m_axi_awvalid_int))
    begin
      m_axi_bready_int <= 0;
      bresp_msg_int <= m_axi_bresp_i;
    end
  end

  // read address handshake
  always_ff @(posedge m_axi_aclk_i, negedge m_axi_aresetn_i)
  begin
    if (!m_axi_aresetn_i)
    begin
      raddr_reg <= 0;
      m_axi_arvalid_int <= 0;
      m_axi_araddr_int <= 0;
      rdata_int <= 0;
    end
    else if (start_read_i & ~m_axi_arvalid_int)
    begin
      raddr_reg <= raddr_i;
      m_axi_arvalid_int <= 1;
      m_axi_araddr_int <= raddr_reg;
    end
    else if (m_axi_arvalid_int & m_axi_arready_i)
    begin
      raddr_reg <= 0;
      m_axi_arvalid_int <= 0;
      m_axi_araddr_int <= 0;
      rdata_int <= m_axi_rdata_i;
    end
  end

  // read response handshake
  always_ff @(posedge m_axi_aclk_i, negedge m_axi_aresetn_i)
  begin
    if (!m_axi_aresetn_i)
    begin
      m_axi_rready_int <= 0;
      rresp_msg_int <= 0;
    end
    else if (start_read_i & ~m_axi_rready_int)
    begin
      m_axi_rready_int <= 1;
    end
    else if (~(m_axi_arvalid_int | m_axi_arready_i) & (m_axi_rvalid_i & m_axi_rready_int))
    begin
      m_axi_rready_int <= 0;
      rresp_msg_int <= m_axi_rresp_i;
    end
  end

  assign m_axi_araddr_o = m_axi_araddr_int;
  assign m_axi_arprot_o = m_axi_arprot_int;
  assign m_axi_arvalid_o = m_axi_arvalid_int;
  assign m_axi_rready_o = m_axi_rready_int;
  assign m_axi_awvalid_o = m_axi_awvalid_int;
  assign m_axi_awaddr_o = m_axi_awaddr_int;
  assign m_axi_awprot_o = m_axi_awprot_int;
  assign m_axi_wvalid_o = m_axi_wvalid_int;
  assign m_axi_wdata_o = m_axi_wdata_int;
  assign m_axi_wstrb_o = m_axi_wstrb_int;
  assign m_axi_bready_o = m_axi_bready_int;
  assign rdata_o = rdata_int;
  assign rresp_msg_o = rresp_msg_int;
  assign bresp_msg_o = bresp_msg_int;
  ////////////////////////////////////////////////////////////////////////////////
  //
  //
  // Formal Verification section begins here.
  //
  //
  ////////////////////////////////////////////////////////////////////////////////
`ifdef FORMAL
// During reset the following interface requirements apply:
// • a master interface must drive ARVALID, AWVALID, and WVALID LOW
// • a slave interface must drive RVALID and BVALID LOW
// • all other signals can be driven to any value. (p A3-36)
master_valids_low_on_reset:
    assert property( @(posedge m_axi_aclk_i)
    (!m_axi_aresetn_i |-> ~(m_axi_wvalid_o | m_axi_arvalid_o | m_axi_awvalid_o)));
slave_valids_low_on_reset:
    assume property( @(posedge m_axi_aclk_i)
    (!m_axi_aresetn_i |-> ~(m_axi_rvalid_i | m_axi_bvalid_i)));

//The earliest point after reset that a master is permitted to begin driving ARVALID, AWVALID, or WVALID HIGH
//is at a rising ACLK edge after ARESETn is HIGH. Figure A3-1 shows the earliest point after reset that ARVALID,
//AWVALID, or WVALID, can be driven HIGH. (p. A3-36)
valids_low_on_first_reset_high:
assume property(@(posedge m_axi_aclk_i)(m_axi_aresetn_i |-> ~(m_axi_rvalid_i | m_axi_bvalid_i)));

// In Figure A3-2, the source presents the address, data or control information after T1 and asserts the VALID signal.
  // "The destination asserts the READY signal after T2, and the source must keep its information stable until the transfer
  // occurs at T3, when this assertion is recognized. (p A3-37)"
// data is held stable while valid is high
property stable_source_data(logic valid, logic [BUS_WIDTH-1:0] data, logic rst_n);
  disable iff (!rst_n)
  valid |-> ##1 ($stable(data) | !valid);
endproperty
    stable_data_ar:
    assert property(@(posedge m_axi_aclk_i) 
    stable_source_data(m_axi_arvalid_o, m_axi_araddr_o, m_axi_aresetn_i));
    stable_data_r:
    assume property(@(posedge m_axi_aclk_i) 
    stable_source_data(m_axi_rvalid_i, m_axi_rdata_i, m_axi_aresetn_i));
    stable_data_aw:
    assert property(@(posedge m_axi_aclk_i) 
    stable_source_data(m_axi_awvalid_o, m_axi_awaddr_o, m_axi_aresetn_i));
    stable_data_w:
    assert property(@(posedge m_axi_aclk_i) 
    stable_source_data(m_axi_wvalid_o, m_axi_wdata_o, m_axi_aresetn_i));
    stable_data_b:
    assume property(@(posedge m_axi_aclk_i) 
    stable_source_data(m_axi_bvalid_i, m_axi_bresp_i, m_axi_aresetn_i));

// Once VALID is asserted it must remain asserted until the handshake occurs, at a rising clock edge at which VALID
// and READY are both asserted. (p A3-37)
property stable_valid_high(logic valid, logic ready, logic rst_n);
  disable iff (!rst_n)
  (valid & ~ready) |-> ##1 valid;
endproperty

valid_stays_high_until_handshake_w:
  assert property( @(posedge m_axi_aclk_i) 
  stable_valid_high(m_axi_wvalid_o, m_axi_wready_i, m_axi_aresetn_i));
valid_stays_high_until_handshake_ar:
  assert property( @(posedge m_axi_aclk_i) 
  stable_valid_high(m_axi_arvalid_o, m_axi_arready_i, m_axi_aresetn_i));
valid_stays_high_until_handshake_aw:
  assert property( @(posedge m_axi_aclk_i) 
  stable_valid_high(m_axi_awvalid_o, m_axi_awready_i, m_axi_aresetn_i));
valid_stays_high_until_handshake_r:
  assume property( @(posedge m_axi_aclk_i) 
  stable_valid_high(m_axi_rvalid_i, m_axi_rready_o, m_axi_aresetn_i));
valid_stays_high_until_handshake_b:
  assume property( @(posedge m_axi_aclk_i) 
  stable_valid_high(m_axi_bvalid_i, m_axi_bready_o, m_axi_aresetn_i));

`endif
                endmodule

