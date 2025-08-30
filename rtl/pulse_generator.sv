module pulse_generator(
    input logic CLK_I,
    input logic RST_I,
    input logic EN_I,
    output logic PULSE_O
);
    logic en_q;

    always_ff @(posedge CLK_I) begin
        if (RST_I) begin
            en_q <= 0;
        end else begin
            en_q <= EN_I;
        end
    end


    always_ff @(posedge CLK_I) begin
        if (RST_I) begin
            PULSE_O <= 0; 
        end else if (!en_q && EN_I) begin
            PULSE_O <= 1;
        end else begin
            PULSE_O <= 0;
        end
    end
endmodule
