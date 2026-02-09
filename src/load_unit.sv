module load_unit (
  input  logic [31:0] rdata_unformatted,
  input  logic [31:0] addr,
  input  logic [4:0]  load_size_onehot,
  output logic [3:0]  rstrb,
  output logic [31:0] rdata_formatted,
  output logic        misaligned_load
);

  logic [31:0] loaded;
  assign loaded = rdata_unformatted >> (8 * addr[1:0]);

  always_comb begin
    misaligned_load = 0;
    rstrb       = 0;
    rdata_formatted  = 0;

    if (load_size_onehot[0]) begin // byte
      rstrb      = 4'h1 << addr[1:0];
      rdata_formatted = {{24{loaded[7]}}, loaded[7:0]};
    end else if (load_size_onehot[1]) begin // byte unsigned
      rstrb      = 4'h1 << addr[1:0];
      rdata_formatted = {{24{1'b0}}, loaded[7:0]};
    end else if (load_size_onehot[2]) begin // half
      misaligned_load = addr[0];
      rstrb       = 4'h3 << (addr[1] * 2);
      rdata_formatted  = {{16{loaded[15]}}, loaded[15:0]};
    end else if (load_size_onehot[3]) begin // half unsigned
      misaligned_load = addr[0];
      rstrb       = 4'h3 << (addr[1] * 2);
      rdata_formatted  = {{16{1'b0}}, loaded[15:0]};
    end else if (load_size_onehot[4]) begin // word
      misaligned_load = |addr[1:0];
      rstrb       = 4'hf;
      rdata_formatted  = loaded;
    end else begin
      rstrb       = 0;
      misaligned_load = 0;
    end
  end

  `ifdef RISCV_FORMAL
  always_comb begin
    // load is never misaligned for byte operations
    if (load_size_onehot[0] || load_size_onehot[1]) begin
      assert (!misaligned_load);
    // load half misaligned when lsb address is nonzero
    end else if (load_size_onehot[2] || load_size_onehot[3]) begin
      if (addr[0]) assert (misaligned_load);
      else assert (!misaligned_load);
    // load word misaligned when any of the 2 lsbs are nonzero
    end else if (load_size_onehot[4]) begin
      if (|addr[1:0]) assert (misaligned_load);
      else assert(!misaligned_load);
    end else begin
      assert(rstrb == 4'd0);
      assert (!misaligned_load);
    end
  end
  `endif
endmodule
