module load_unit
  import params_pkg::*;
(
    input mem_op_t mem_op_i,
    input logic [1:0] raddr_lower2_i,
    input logic [31:0] rdata_unformatted_i,
    output logic misaligned_load_o,
    output logic [3:0] rstrb_o,
    output logic [31:0] rdata_o
);
  logic [31:0] loaded;
  logic misaligned_load;
  logic [3:0] strb;
  logic [31:0] load_formatted;
  assign loaded = rdata_unformatted_i >> 8 * (raddr_lower2_i);
  // logic to determine which bits of the read data from data memory will be loaded for load instructions
  always_comb begin
    misaligned_load = 0;
    strb = 4'h0;
    load_formatted = 32'd0;
    case (mem_op_i)
      //lw
      MEM_LW: begin
        strb = 4'hf;
        load_formatted = loaded;
      end
      //lb
      MEM_LB: begin
        strb = 4'h1;
        load_formatted = {{24{loaded[7]}}, loaded[7:0]};
      end
      //lbu
      MEM_LBU: begin
        strb = 4'h1;
        load_formatted = {{24{1'b0}}, loaded[7:0]};
      end
      //lh
      MEM_LH: begin
        strb = 4'h3;
        load_formatted = {{16{loaded[15]}}, loaded[15:0]};
      end
      //lhu
      MEM_LHU: begin
        strb = 4'h3;
        load_formatted = {{16{1'b0}}, loaded[15:0]};
      end
      default: ;
    endcase
  end
  assign rstrb_o       = misaligned_load ? 0 : strb;
  assign load_trap_mcause_o = misaligned_load ? {1'b0, TRAP_CODE_LOAD_ADDR_MISALIGNED} : 0;
  assign misaligned_load_o  = misaligned_load;
  assign rdata_o = load_formatted;
endmodule
