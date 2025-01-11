`include "macros.svh"
module dtcore32_MEM_stage(
`ifdef RISCV_FORMAL
    output logic [`NRET * `XLEN/8 - 1 : 0] MEM_rvfi_mem_rmask_o,
`endif
    input logic clk_i,
    input logic rst_i,
    //inputs from IE/DM register
    //control
    input logic 	   	MEM_reg_write_i,
    input logic [1:0] 	MEM_result_src_i,
    input logic [2:0] 	MEM_load_size_i,
    //data
    input logic [31:0] 	MEM_alu_result_i,
    input logic [31:0] 	MEM_pc_plus_4_i,
    input logic [4:0]  	MEM_dest_reg_i,
    //input from data memory
    input logic [31:0] 	MEM_read_data_tick_i,
    //outputs from DM/WB register

    //connects to decode stage
    output logic   		WB_reg_write_o,
    //connects to hazard unit and decode stage
    output logic   [4:0] 	WB_dest_reg_o,
    //connects to writeback stage
    output logic   [1:0] 	WB_result_src_o,
    output logic   [31:0] WB_alu_result_o,
    output logic   [31:0] WB_read_data_o,
    output logic   [31:0] WB_pc_plus_4_o
  );

  // ===========================================================================
  // 			          Parameters, Registers, and Wires
  // ===========================================================================

  logic [31:0] MEM_read_data;
  logic [1:0] byte_num;
  // ===========================================================================
  // 			          Implementation
  // ===========================================================================

  assign byte_num = MEM_alu_result_i[1:0];

  always_comb
  begin
    case (MEM_load_size_i)
      //lw
      3'b000:
      begin
        MEM_read_data = MEM_read_data_tick_i;
`ifdef RISCV_FORMAL

        MEM_rvfi_mem_rmask_o = 4'hf;
`endif

      end
      //lb
      3'b001:
      case(byte_num)
        2'b00:
        begin
          MEM_read_data = { {24{MEM_read_data_tick_i[7]}}, MEM_read_data_tick_i[7:0] };
`ifdef RISCV_FORMAL

          MEM_rvfi_mem_rmask_o = 4'h1;
`endif

        end
        2'b01:
        begin
          MEM_read_data = { {24{MEM_read_data_tick_i[15]}}, MEM_read_data_tick_i[15:8] };
`ifdef RISCV_FORMAL

          MEM_rvfi_mem_rmask_o = 4'h2;
`endif

        end
        2'b10:
        begin
          MEM_read_data = { {24{MEM_read_data_tick_i[23]}}, MEM_read_data_tick_i[23:16] };
`ifdef RISCV_FORMAL

          MEM_rvfi_mem_rmask_o = 4'h4;
`endif

        end
        2'b11:
        begin
          MEM_read_data = { {24{MEM_read_data_tick_i[31]}}, MEM_read_data_tick_i[31:24] };
`ifdef RISCV_FORMAL

          MEM_rvfi_mem_rmask_o = 4'h8;
`endif

        end
      endcase
      //lbu
      3'b010:
      case(byte_num)
        2'b00:
        begin
          MEM_read_data = { {24{1'b0}},MEM_read_data_tick_i[7:0] };
`ifdef RISCV_FORMAL

          MEM_rvfi_mem_rmask_o = 4'h1;
`endif

        end
        2'b01:
        begin
          MEM_read_data = { {24{1'b0}},MEM_read_data_tick_i[15:8] };
`ifdef RISCV_FORMAL

          MEM_rvfi_mem_rmask_o = 4'h2;
`endif

        end
        2'b10:
        begin
          MEM_read_data = { {24{1'b0}},MEM_read_data_tick_i[23:16] };
`ifdef RISCV_FORMAL

          MEM_rvfi_mem_rmask_o = 4'h4;
`endif

        end
        2'b11:
        begin
          MEM_read_data = { {24{1'b0}},MEM_read_data_tick_i[31:24] };
`ifdef RISCV_FORMAL

          MEM_rvfi_mem_rmask_o = 4'h8;
`endif

        end
      endcase

      //lh
      3'b011:
      case(byte_num[1])
        1'b0:
        begin
          MEM_read_data = { {16{MEM_read_data_tick_i[15]}},MEM_read_data_tick_i[15:0] };
`ifdef RISCV_FORMAL

          MEM_rvfi_mem_rmask_o = 4'h3;
`endif

        end
        1'b1:
        begin
          MEM_read_data = { {16{MEM_read_data_tick_i[31]}},MEM_read_data_tick_i[31:16] };
`ifdef RISCV_FORMAL

          MEM_rvfi_mem_rmask_o = 4'hc;
`endif

        end
      endcase

      //lhu
      3'b100:
      case(byte_num[1])
        1'b0:
        begin
          MEM_read_data = { {16{1'b0}},MEM_read_data_tick_i[15:0] };
`ifdef RISCV_FORMAL

          MEM_rvfi_mem_rmask_o = 4'h3;
`endif

        end
        1'b1:
        begin
          MEM_read_data = { {16{1'b0}},MEM_read_data_tick_i[31:16] };
`ifdef RISCV_FORMAL

          MEM_rvfi_mem_rmask_o = 4'hc;
`endif

        end
      endcase

      default:
      begin
        MEM_read_data = 32'dx;
`ifdef RISCV_FORMAL

        MEM_rvfi_mem_rmask_o = 4'hx;
`endif

      end
    endcase
  end

  // MEM/WB register
  always_ff@(posedge clk_i)
  begin
    if(rst_i)
    begin
      // signals for NOP
      WB_alu_result_o <= 0;
      WB_read_data_o <= 0;
      WB_pc_plus_4_o <= 0;
      WB_dest_reg_o <= 0;
      WB_reg_write_o <= 0;
      WB_result_src_o <= 0;
    end
    else
    begin
      WB_alu_result_o <= MEM_alu_result_i;
      WB_read_data_o <= MEM_read_data;
      WB_pc_plus_4_o <= MEM_pc_plus_4_i;
      WB_dest_reg_o <= MEM_dest_reg_i;
      WB_reg_write_o <= MEM_reg_write_i;
      WB_result_src_o <= MEM_result_src_i;
    end
  end
endmodule
