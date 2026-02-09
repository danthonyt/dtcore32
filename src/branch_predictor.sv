module branch_predictor #(PHT_WIDTH = 6)(
  input  logic        clk_i,
  input  logic        rst_i,
  input  logic        id_is_branch,
  input  logic [31:0] id_pc,
  input  logic        mem_is_branch,
  input  logic        mem_jump_taken,
  input  logic [PHT_WIDTH-1:0]  mem_pht_idx,
  output logic        predict_btaken,
  output logic [PHT_WIDTH-1:0]  id_pht_idx
);

  logic  [5:0] ght;
  logic  [1:0] pht [0:(2**PHT_WIDTH-1)];
  logic [PHT_WIDTH-1:0] pht_idx;
  integer pht_loop_idx;

  assign pht_idx = id_is_branch ? id_pc[7:2] ^ ght : 0;
  assign predict_btaken = id_is_branch ? pht[pht_idx][1] : 0;
  assign id_pht_idx        = pht_idx;

  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      ght <= 0;
      for (pht_loop_idx = 0; pht_loop_idx < 2**PHT_WIDTH; pht_loop_idx = pht_loop_idx + 1) begin
        pht[pht_loop_idx] <= 2'b01;
      end
    end else begin
      if (mem_is_branch) begin
        ght <= {ght[4:0], mem_jump_taken};
        if (mem_jump_taken && (pht[mem_pht_idx] != 2'b11)) begin
          pht[mem_pht_idx] <= pht[mem_pht_idx] + 1;
        end else if (!mem_jump_taken && (pht[mem_pht_idx] != 2'b00)) begin
          pht[mem_pht_idx] <= pht[mem_pht_idx] - 1;
        end
      end
    end
  end

  `ifdef RISCV_FORMAL
//=================================================================
// Branch Predictor Assertions
//=================================================================
always_comb begin
    // --------------------------
    // PHT entry bounds
    // --------------------------
    for (int i = 0; i < 2**PHT_WIDTH; i++) begin
        assert(pht[i] >= 2'b00);
        assert(pht[i] <= 2'b11);
    end

    // --------------------------
    // GHT width sanity
    // --------------------------
    assert(ght < 2**6); // 6-bit global history table

    // --------------------------
    // PHT index bounds
    // --------------------------
    assert(pht_idx < 2**PHT_WIDTH);

    // --------------------------
    // Prediction outputs
    // --------------------------
    if (!id_is_branch) begin
        assert(predict_btaken == 0);
        assert(id_pht_idx == 0);
    end 
end
`endif


endmodule
