module adder#(parameter WIDTH = 32)
(
    input logic [WIDTH-1:0] in1,
    input logic [WIDTH-1:0] in2,
    output logic [WIDTH-1:0] sum
);
assign sum = in1 + in2;
endmodule
