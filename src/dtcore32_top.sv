module dtcore32_top (
    input logic clk_i,
    input logic rst_i,
    output logic [31:0] IMEM_rd_data_out,   // Added dummy output to retain IMEM signals
    output logic [31:0] DMEM_rd_data_out
);

    // Internal signals
    logic [31:0] IMEM_addr;
    logic [31:0] IMEM_rd_data;
    logic [3:0] DMEM_wr_byte_en;
    logic [31:0] DMEM_wr_data;
    logic [31:0] DMEM_addr;
    logic [31:0] DMEM_rd_data;

    // Instantiate memory modules
    dtcore32_imem dtcore32_imem_inst (
        .IMEM_addr_i(IMEM_addr),
        .IMEM_rd_data_o(IMEM_rd_data)
    );
    
    dtcore32_dmem dtcore32_dmem_inst (
        .clk_i(clk_i),
        .rst_i(rst_i),
        .DMEM_wr_byte_en_i(DMEM_wr_byte_en),
        .DMEM_wr_data_i(DMEM_wr_data),
        .DMEM_addr_i(DMEM_addr),
        .DMEM_rd_data_o(DMEM_rd_data)
    );

    // Instantiate CPU core
    dtcore32 dtcore32_inst (
        .clk_i(clk_i),
        .rst_i(rst_i),
        .IMEM_rd_data_i(IMEM_rd_data),
        .DMEM_rd_data_i(DMEM_rd_data),
        .IMEM_addr_o(IMEM_addr),
        .DMEM_addr_o(DMEM_addr),
        .DMEM_wr_data_o(DMEM_wr_data),
        .DMEM_wr_byte_en_o(DMEM_wr_byte_en),
        .exception_o()
    );

    // Retain IMEM_rd_data for synthesis (can be analyzed or connected to a peripheral)
    assign IMEM_rd_data_out = IMEM_rd_data;
    assign DMEM_rd_data_out = DMEM_rd_data;

endmodule
