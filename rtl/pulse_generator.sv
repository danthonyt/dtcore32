module pulse_generator(
    input logic clk_i,
    input logic rst_i,
    input logic en_i,
    output logic pulse_o
);
    logic en_q;

    always_ff @(posedge clk_i) begin
        if (rst_i) begin
            en_q <= 0;
        end else begin
            en_q <= en_i;
        end
    end


    always_ff @(posedge clk_i) begin
        if (rst_i) begin
            pulse_o <= 0; 
        end else if (!en_q && en_i) begin
            pulse_o <= 1;
        end else begin
            pulse_o <= 0;
        end
    end
endmodule
