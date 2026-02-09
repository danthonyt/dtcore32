module store_unit (
  input  logic [31:0] addr,
  input  logic [31:0] wdata_unformatted,
  input  logic [2:0]  store_size_onehot,
  output logic [31:0] wdata_formatted,
  output logic [3:0]  wstrb,
  output logic        misaligned_store
);

  always_comb begin
    misaligned_store = 0;
    wdata_formatted      = 0;
    wstrb        = 0;

    if (store_size_onehot[0]) begin // byte
      // never misaligned
      wstrb   = 4'b1 << addr[1:0];
      wdata_formatted = wdata_unformatted << (addr[1:0] * 8);
    end else if (store_size_onehot[1]) begin // half
      // misaligned when lsb = 1
      misaligned_store = addr[0];
      wstrb        = 4'h3 << (addr[1] * 2);
      wdata_formatted      = wdata_unformatted << (addr[1] * 16);
    end else if (store_size_onehot[2]) begin // word
      // misaligned when lsbs[1:0] != 2'b00
      misaligned_store = |addr[1:0];
      wstrb        = 4'hf;
      wdata_formatted      = wdata_unformatted;
    end else begin
      wstrb        = 0;
      misaligned_store = 0;
    end
  end

  `ifdef RISCV_FORMAL
  always_comb begin
    // byte store is never misaligned
    if (store_size_onehot[0] ) begin
      assert (!misaligned_store);
    // half store is misaligned when lsb address = 1
    end else if (store_size_onehot[1]) begin
      if (addr[0]) assert (misaligned_store);
      else assert (!misaligned_store);
    // word store is misaligned when 2 lsbs have one nonzero digit
    end else if (store_size_onehot[2]) begin
      if (|addr[1:0]) assert (misaligned_store);
      else assert(!misaligned_store);
    end else begin
      assert(wstrb == 4'd0);
      assert (!misaligned_store);
    end
  end
  `endif
endmodule
