module branch_predictor (
  input  logic        clk_i,
  input  logic        rst_i,
  input  logic        id_is_branch,
  input  logic [31:0] id_q_pc,
  input  logic        mem_q_is_branch,
  input  logic        mem_q_jump_taken,
  input  logic [5:0]  mem_q_pht_idx,
  output logic        id_predict_btaken,
  output logic [5:0]  id_pht_idx
);

  reg  [5:0] ght;
  reg  [1:0] pht [0:63];
  wire [5:0] pht_idx;
  integer pht_loop_idx;

  assign pht_idx = id_is_branch ? id_q_pc[7:2] ^ ght : 0;
  assign id_predict_btaken = id_is_branch ? pht[pht_idx][1] : 0;
  assign id_pht_idx        = pht_idx;

  always @(posedge clk_i) begin
    if (rst_i) begin
      ght <= 0;
      for (pht_loop_idx = 0; pht_loop_idx < 64; pht_loop_idx = pht_loop_idx + 1) begin
        pht[pht_loop_idx] <= 2'b01;
      end
    end else begin
      if (mem_q_is_branch) begin
        ght <= {ght[4:0], mem_q_jump_taken};
        if (mem_q_jump_taken && (pht[mem_q_pht_idx] != 2'b11)) begin
          pht[mem_q_pht_idx] <= pht[mem_q_pht_idx] + 1;
        end else if (!mem_q_jump_taken && (pht[mem_q_pht_idx] != 2'b00)) begin
          pht[mem_q_pht_idx] <= pht[mem_q_pht_idx] - 1;
        end
      end
    end
  end

endmodule
