module dtcore32_imem (
    input logic [31:0] IMEM_addr_i,
    output logic [31:0] IMEM_rd_data_o
);
parameter IMEM_DEPTH = 32'hf;
logic [31:0] IMEM[0:IMEM_DEPTH];


// IMEM is read combinationally -- no delay
// address is byte addressable, so drop the least significant 2 bits to make word aligned
assign IMEM_rd_data_o = IMEM[IMEM_addr_i[31:2]];
initial
    $readmemh("add_imem.mem",IMEM);

endmodule