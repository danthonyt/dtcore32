module dtcore32_axi_lite_master#(
    parameter BUS_WIDTH = 32
  )(
    // global signals
    input logic                           m_axi_aclk_i,
    input logic                           m_axi_aresetn_i,
    // read address channel
    output logic [31:0]                   m_axi_araddr_o,
    output logic [3:0]                    m_axi_arcache_o,
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
    output logic [BUS_WIDTH-1:0]           m_axi_wdata_i,
    output logic [(BUS_BYTE_WIDTH/8)-1:0]  m_axi_wstrb_i,
    // write response channel
    input  logic                          m_axi_bvalid_i,
    output logic                          m_axi_bready_o,
    input logic [1:0]                     m_axi_bresp_i

    // Read FSM
    input logic read_fsm_start_i,
    input logic [31:0] raddr_i,
    output logic [BUS_WIDTH-1:0] rdata_o,
    output logic rresp_msg_o,
    output logic read_fsm_done_o,
    
    // Write FSM
    input logic write_fsm_start_i,
    input logic [31:0] wraddr_i,
    input logic [BUS_WIDTH-1:0] wrdata_i,
    output logic [1:0] bresp_msg_o,
    output logic write_fsm_done_o

  );

  ////////////////////////////////////////////////////////////////////////////////
  //
  //
  // WRITE FSM
  //
  //
  ////////////////////////////////////////////////////////////////////////////////
  typedef enum logic [1:0] {WRITE_RESET,WRITE_IDLE,WRITE_WAIT,WRITE_RESP} write_states_t;
  write_states_t write_fsm_state;

  // FSM 1 process block
  always_ff(posedge m_axi_aclk_i or negedge m_axi_aresetn_i)
    if ( !m_axi_aresetn_i)
    begin
      m_axi_awvalid_int <= 0;
      m_axi_wvalid_int <= 0;
      m_axi_awaddr_int <= 0;
      m_axi_wdata_int <= 0;
      m_axi_bready_int <= 0;
      m_axi_wstrb_int <= 0;
      bresp_msg_int <= 0;
      read_fsm_done_int <= 0;
      write_fsm_state <= WRITE_RESET;
    end
    else
    begin
      case (write_fsm_state)
        WRITE_RESET:
        begin
          write_fsm_state <= WRITE_IDLE;
        end
        WRITE_IDLE: // wait for start signal to begin the write transaction
        begin
          m_axi_awvalid_o <= 0;
          m_axi_wvalid_o <= 0;
          m_axi_awaddr_o <= 0;
          m_axi_wdata_o <= 0;
          m_axi_bready_o <= 0;
          m_axi_wstrb_o <= 0;
          bresp_msg_o <= 0;
          write_fsm_done_o <= 0;
          if (write_fsm_start_i == 1)
          begin
            m_axi_awvalid_o <= 1;
            m_axi_wvalid_o <= 1;
            m_axi_awaddr_o <= wraddr_i;
            m_axi_wdata_o <= wrdata_i;
            m_axi_bready_o <= 1;
            m_axi_wstrb_o <= 8'hff;
            write_fsm_state <= WRITE_WAIT;
          end
        end
        WRITE_WAIT: // wait for the addressed slave to be ready, then deassert valid signals
        begin
          if ((m_axi_awready_i & m_axi_wready_i) == 1)
          begin
            m_axi_awvalid_o <= 0;
            m_axi_wvalid_o <= 0;
            write_fsm_state <= WRITE_RESP;
          end
        end
        WRITE_RESP: // read the write response from the slave when it's ready
        begin
          if (m_axi_bvalid_i == 1)
          begin
            bresp_msg_o <= m_axi_bresp_i;
            write_fsm_done_o <= 1;
            write_fsm_state <= WRITE_IDLE;
          end
        end
      endcase
    end
  ////////////////////////////////////////////////////////////////////////////////
  //
  //
  // READ FSM
  //
  //
  ////////////////////////////////////////////////////////////////////////////////
  typedef enum logic [1:0] {READ_RESET,READ_IDLE,READ_ADDR,WRITE_WAIT} read_states_t;
  read_states_t read_fsm_state;

  // FSM 1 process block
  always_ff(posedge m_axi_aclk_i or negedge m_axi_aresetn_i)
    if ( !m_axi_aresetn_i)
    begin
      read_state <= READ_RESET;
      m_axi_arvalid_o <= 0;
      m_axi_rready_o <= 0;
      m_axi_araddr_o <= 0;
      rresp_msg_o <= 0;
      rdata_o <= 0;
      read_fsm_done_o <= 0;
    end
    else
    begin
      case (read_fsm_state)
        READ_RESET:
        begin
          read_fsm_state <= READ_IDLE;
        end
        READ_IDLE: // wait for start signal to begin the read transaction
        begin
          m_axi_arvalid_o <= 0;
          m_axi_rready_o <= 0;
          m_axi_araddr_o <= 0;
          rresp_msg_o <= 0;
          rdata_o <= 0;
          read_fsm_done_o <= 0;
          if (read_fsm_start_i == 1)
          begin
            m_axi_arvalid_o <= 1;
            m_axi_rready_o <= 1;
            m_axi_araddr_o <= raddr_i;
            read_fsm_state <= READ_ADDR;
          end
        end
        READ_ADDR: // wait for the addressed slave to be ready, then deassert arvalid
        begin
          if (m_axi_arready_i == 1)
          begin
            m_axi_arvalid_o <= 0;
            read_fsm_state <= READ_WAIT;
          end
        end
        READ_WAIT: // read the response and read data from the slave when it's ready
        begin
          if (m_axi_rvalid_i == 1)
          begin
            rresp_msg_o <= m_axi_rresp_i;
            m_axi_rready_o <= 0;
            rdata_o <= m_axi_rdata_i;
            read_fsm_done_o <= 1;
            read_fsm_state <= READ_IDLE;
          end
        end
      endcase
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

