module ff_nen_clr #(parameter WIDTH = 1)(
    input logic clk,
    input logic rst,
    input logic en_n,
    input logic clr,
    input logic [WIDTH-1:0] d,
    output logic [WIDTH-1:0] q
);
always_ff @(posedge clk)begin
    if (rst) q <= 0;
    else if (clr) q <= 0;
    else if (!en_n) q <= d;
end
endmodule
