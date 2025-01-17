`include "macros.svh"
module dtcore32_MEM_stage (
    input logic clk_i,
    input logic rst_i,
    
    // DMEM
    input logic [31:0] DMEM_rd_data_i,
    output logic [31:0] DMEM_wr_data_o,
    output logic [3:0] DMEM_wr_byte_en_o,

    // WB stage
    input logic EX_reg_wr_en_i,
    input logic [1:0] EX_result_src_i,
    input logic [2:0] EX_load_size_i,
    input logic [1:0] EX_mem_wr_size_i,
    input logic [31:0] EX_alu_result_i,
    input logic [31:0] EX_dmem_wr_data_i,
    input logic [11:7] EX_dest_reg_i,
    input logic [31:0] EX_pc_plus_4_i,

    // MEM stage
    input logic MEM_stall_i,
    output logic MEM_reg_wr_en_o,
    output logic [1:0] MEM_result_src_o,
    output logic [31:0] MEM_alu_result_o,
    output logic [11:7] MEM_dest_reg_o,
    output logic [31:0] MEM_pc_plus_4_o,
    output logic [31:0] MEM_dmem_rd_data_o,
    output logic MEM_exception_o

  );

  logic MEM_misaligned_store;
  logic MEM_misaligned_load;
  logic MEM_unknown_load;

  logic [2:0] MEM_load_size;
  logic [1:0] MEM_mem_wr_size;
  logic [31:0] MEM_dmem_wr_data;

  assign MEM_exception_o = MEM_misaligned_load | MEM_misaligned_store | MEM_unknown_load;

  // EX/MEM register
  always_ff @(posedge clk_i)
  begin
    if (rst_i)
    begin
      MEM_reg_wr_en_o <= 0;
      MEM_result_src_o <= 0;
      MEM_load_size <= 0;
      MEM_mem_wr_size <= 0;
      MEM_alu_result_o <= 0;
      MEM_dmem_wr_data <= 0;
      MEM_dest_reg_o <= 0;
      MEM_pc_plus_4_o <= 0;
    end
    else if (!MEM_stall_i)
    begin
      MEM_reg_wr_en_o <= EX_reg_wr_en_i;
      MEM_result_src_o <= EX_result_src_i;
      MEM_load_size <= EX_load_size_i;
      MEM_mem_wr_size <= EX_mem_wr_size_i;
      MEM_alu_result_o <= EX_alu_result_i;
      MEM_dmem_wr_data <= EX_dmem_wr_data_i;
      MEM_dest_reg_o <= EX_dest_reg_i;
      MEM_pc_plus_4_o <= EX_pc_plus_4_i;
    end
  end
  // logic to determine which bytes are written to data memory for store instructions
  always_comb
  begin
    MEM_misaligned_store = 0;
    DMEM_wr_data_o = 0;
    DMEM_wr_byte_en_o = 0;
    case (MEM_mem_wr_size)
      `MEM_NO_DMEM_WR:
      begin
      end
      `MEM_WORD_WR:
      begin
        DMEM_wr_data_o = MEM_dmem_wr_data;
        DMEM_wr_byte_en_o = 4'hf;
      end
      `MEM_HALF_WR:
      begin
        case (MEM_alu_result_o[1:0])
          2'b00:
          begin
            DMEM_wr_byte_en_o = 4'h3;
            DMEM_wr_data_o = {16'd0,MEM_dmem_wr_data[15:0]};
          end
          2'b10:
          begin
            DMEM_wr_byte_en_o = 4'hc;
            DMEM_wr_data_o = {MEM_dmem_wr_data[15:0],16'd0};
          end
          default:
            MEM_misaligned_store = 1;
        endcase

      end
      `MEM_BYTE_WR:
      begin
        case (MEM_alu_result_o[1:0])
          2'b00:
          begin
            DMEM_wr_byte_en_o = 4'h1;
            DMEM_wr_data_o = {24'd0,MEM_dmem_wr_data[7:0]};
          end
          2'b01:
          begin
            DMEM_wr_byte_en_o = 4'h2;
            DMEM_wr_data_o = {16'd0,MEM_dmem_wr_data[7:0],8'd0};
          end
          2'b10:
          begin
            DMEM_wr_byte_en_o = 4'h4;
            DMEM_wr_data_o = {8'd0,MEM_dmem_wr_data[7:0],16'd0};
          end
          2'b11:
          begin
            DMEM_wr_byte_en_o = 4'h8;
            DMEM_wr_data_o = {MEM_dmem_wr_data[7:0],24'd0};
          end
          default:
            MEM_misaligned_store = 1;
        endcase
      end
    endcase
  end

  // logic to determine which bits of the read data from data memory will be loaded for load instructions
  always_comb
  begin
    MEM_misaligned_load = 0;
    MEM_unknown_load = 0;
    MEM_dmem_rd_data_o = 0;
    case (MEM_load_size)
      //lw
      `DMEM_LOAD_SIZE_WORD:
      begin
        MEM_dmem_rd_data_o = DMEM_rd_data_i;
      end
      //lb
      `DMEM_LOAD_SIZE_BYTE:
      case(MEM_alu_result_o[1:0])
        2'b00:
        begin
          MEM_dmem_rd_data_o = { {24{DMEM_rd_data_i[7]}}, DMEM_rd_data_i[7:0] };
        end
        2'b01:
        begin
          MEM_dmem_rd_data_o = { {24{DMEM_rd_data_i[15]}}, DMEM_rd_data_i[15:8] };
        end
        2'b10:
        begin
          MEM_dmem_rd_data_o = { {24{DMEM_rd_data_i[23]}}, DMEM_rd_data_i[23:16] };
        end
        2'b11:
        begin
          MEM_dmem_rd_data_o = { {24{DMEM_rd_data_i[31]}}, DMEM_rd_data_i[31:24] };
        end
      endcase
      //lbu
      `DMEM_LOAD_SIZE_BYTEU:
      case(MEM_alu_result_o[1:0])
        2'b00:
        begin
          MEM_dmem_rd_data_o = { {24{1'b0}},DMEM_rd_data_i[7:0] };
        end
        2'b01:
        begin
          MEM_dmem_rd_data_o = { {24{1'b0}},DMEM_rd_data_i[15:8] };
        end
        2'b10:
        begin
          MEM_dmem_rd_data_o = { {24{1'b0}},DMEM_rd_data_i[23:16] };
        end
        2'b11:
        begin
          MEM_dmem_rd_data_o = { {24{1'b0}},DMEM_rd_data_i[31:24] };
        end
      endcase
      //lh
      `DMEM_LOAD_SIZE_HALF:
      case(MEM_alu_result_o[1:0])
        2'b00:
        begin
          MEM_dmem_rd_data_o = { {16{DMEM_rd_data_i[15]}},DMEM_rd_data_i[15:0] };
        end
        2'b10:
        begin
          MEM_dmem_rd_data_o = { {16{DMEM_rd_data_i[31]}},DMEM_rd_data_i[31:16] };
        end
        default:
          MEM_misaligned_load = 1;
      endcase

      //lhu
      `DMEM_LOAD_SIZE_HALFU:
      case(MEM_alu_result_o[1:0])
        2'b00:
        begin
          MEM_dmem_rd_data_o = { {16{1'b0}},DMEM_rd_data_i[15:0] };
        end
        2'b10:
        begin
          MEM_dmem_rd_data_o = { {16{1'b0}},DMEM_rd_data_i[31:16] };
        end
        default:
          MEM_misaligned_load = 1;

      endcase

      default:
        MEM_unknown_load = 1;
    endcase
  end

endmodule
