`include "macros.svh"
module dtcore32_MEM_stage (
    input logic [2:0] MEM_load_size_i,
    input logic [1:0] MEM_mem_wr_size_i,
    input logic [31:0] MEM_alu_result_i,
    input logic [31:0] MEM_dmem_wr_data_i,
    input logic [31:0] DMEM_rd_data_i,
    output logic [31:0] MEM_dmem_rd_data_o,
    output logic [3:0] DMEM_wr_byte_en_o,
    output logic [31:0] DMEM_wr_data_o,
    output logic MEM_misaligned_store_o,
    output logic MEM_misaligned_load_o,
    output logic MEM_unknown_load_o

  );
  logic [31:0] MEM_dmem_rd_data;
  logic [3:0] DMEM_wr_byte_en;
  logic [31:0] DMEM_wr_data;
  logic MEM_misaligned_store;
  logic MEM_misaligned_load;
  logic MEM_unknown_load;


  // stores
  always_comb
  begin
    MEM_misaligned_store = 0;
    DMEM_wr_data = 0;
    DMEM_wr_byte_en = 0;
    case (MEM_mem_wr_size_i)
      `MEM_NO_DMEM_WR:
      begin
      end
      `MEM_WORD_WR:
      begin
        DMEM_wr_data = MEM_dmem_wr_data_i;
        DMEM_wr_byte_en = 4'hf;
      end
      `MEM_HALF_WR:
      begin
        case (MEM_alu_result_i[1:0])
          2'b00:
          begin
            DMEM_wr_byte_en = 4'h3;
            DMEM_wr_data = {16'd0,MEM_dmem_wr_data_i[15:0]};
          end
          2'b10:
          begin
            DMEM_wr_byte_en = 4'hc;
            DMEM_wr_data = {MEM_dmem_wr_data_i[15:0],16'd0};
          end
          default:
            MEM_misaligned_store = 1;
        endcase

      end
      `MEM_BYTE_WR:
      begin
        case (MEM_alu_result_i[1:0])
          2'b00:
          begin
            DMEM_wr_byte_en = 4'h1;
            DMEM_wr_data = {24'd0,MEM_dmem_wr_data_i[7:0]};
          end
          2'b01:
          begin
            DMEM_wr_byte_en = 4'h2;
            DMEM_wr_data = {16'd0,MEM_dmem_wr_data_i[7:0],8'd0};
          end
          2'b10:
          begin
            DMEM_wr_byte_en = 4'h4;
            DMEM_wr_data = {8'd0,MEM_dmem_wr_data_i[7:0],16'd0};
          end
          2'b11:
          begin
            DMEM_wr_byte_en = 4'h8;
            DMEM_wr_data = {MEM_dmem_wr_data_i[7:0],24'd0};
          end
          default:
            MEM_misaligned_store = 1;
        endcase
      end
    endcase
  end

  // loads
  always_comb
  begin
    MEM_misaligned_load = 0;
    MEM_unknown_load = 0;
    MEM_dmem_rd_data = 0;
    case (MEM_load_size_i)
      //lw
      `DMEM_LOAD_SIZE_WORD:
      begin
        MEM_dmem_rd_data = DMEM_rd_data_i;
      end
      //lb
      `DMEM_LOAD_SIZE_BYTE:
      case(MEM_alu_result_i[1:0])
        2'b00:
        begin
          MEM_dmem_rd_data = { {24{DMEM_rd_data_i[7]}}, DMEM_rd_data_i[7:0] };
        end
        2'b01:
        begin
          MEM_dmem_rd_data = { {24{DMEM_rd_data_i[15]}}, DMEM_rd_data_i[15:8] };
        end
        2'b10:
        begin
          MEM_dmem_rd_data = { {24{DMEM_rd_data_i[23]}}, DMEM_rd_data_i[23:16] };
        end
        2'b11:
        begin
          MEM_dmem_rd_data = { {24{DMEM_rd_data_i[31]}}, DMEM_rd_data_i[31:24] };
        end
      endcase
      //lbu
      `DMEM_LOAD_SIZE_BYTEU:
      case(MEM_alu_result_i[1:0])
        2'b00:
        begin
          MEM_dmem_rd_data = { {24{1'b0}},DMEM_rd_data_i[7:0] };
        end
        2'b01:
        begin
          MEM_dmem_rd_data = { {24{1'b0}},DMEM_rd_data_i[15:8] };
        end
        2'b10:
        begin
          MEM_dmem_rd_data = { {24{1'b0}},DMEM_rd_data_i[23:16] };
        end
        2'b11:
        begin
          MEM_dmem_rd_data = { {24{1'b0}},DMEM_rd_data_i[31:24] };
        end
      endcase
      //lh
      `DMEM_LOAD_SIZE_HALF:
      case(MEM_alu_result_i[1:0])
        2'b00:
        begin
          MEM_dmem_rd_data = { {16{DMEM_rd_data_i[15]}},DMEM_rd_data_i[15:0] };
        end
        2'b10:
        begin
          MEM_dmem_rd_data = { {16{DMEM_rd_data_i[31]}},DMEM_rd_data_i[31:16] };
        end
        default:
          MEM_misaligned_load = 1;
      endcase

      //lhu
      `DMEM_LOAD_SIZE_HALFU:
      case(MEM_alu_result_i[1:0])
        2'b00:
        begin
          MEM_dmem_rd_data = { {16{1'b0}},DMEM_rd_data_i[15:0] };
        end
        2'b10:
        begin
          MEM_dmem_rd_data = { {16{1'b0}},DMEM_rd_data_i[31:16] };
        end
        default:
          MEM_misaligned_load = 1;

      endcase

      default:
        MEM_unknown_load = 1;
    endcase
  end


  assign MEM_dmem_rd_data_o = MEM_dmem_rd_data;
  assign DMEM_wr_byte_en_o = DMEM_wr_byte_en;
  assign DMEM_wr_data_o = DMEM_wr_data;
  assign MEM_misaligned_store_o = MEM_misaligned_store;
  assign MEM_misaligned_load_o = MEM_misaligned_load;
  assign MEM_unknown_load_o = MEM_unknown_load;
endmodule
