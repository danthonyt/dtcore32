module load_size_conv
  (
    input logic [2:0] load_size,
    input logic [1:0] byte_num,
    input logic [31:0] rd_data,
    output logic [31:0] converted_data
  );

  always_comb
  begin
    case (load_size)
      //lw
      3'b000:
      begin
        converted_data = rd_data;

      end
      //lb
      3'b001:
      case(byte_num)
        2'b00:
        begin
          converted_data = { {24{rd_data[7]}}, rd_data[7:0] };

        end
        2'b01:
        begin
          converted_data = { {24{rd_data[15]}}, rd_data[15:8] };

        end
        2'b10:
        begin
          converted_data = { {24{rd_data[23]}}, rd_data[23:16] };

        end
        2'b11:
        begin
          converted_data = { {24{rd_data[31]}}, rd_data[31:24] };

        end
      endcase
      //lbu
      3'b010:
      case(byte_num)
        2'b00:
        begin
          converted_data = { {24{1'b0}},rd_data[7:0] };

        end
        2'b01:
        begin
          converted_data = { {24{1'b0}},rd_data[15:8] };

        end
        2'b10:
        begin
          converted_data = { {24{1'b0}},rd_data[23:16] };


        end
        2'b11:
        begin
          converted_data = { {24{1'b0}},rd_data[31:24] };


        end
      endcase

      //lh
      3'b011:
      case(byte_num[1])
        1'b0:
        begin
          converted_data = { {16{rd_data[15]}},rd_data[15:0] };


        end
        1'b1:
        begin
          converted_data = { {16{rd_data[31]}},rd_data[31:16] };


        end
      endcase

      //lhu
      3'b100:
      case(byte_num[1])
        1'b0:
        begin
          converted_data = { {16{1'b0}},rd_data[15:0] };


        end
        1'b1:
        begin
          converted_data = { {16{1'b0}},rd_data[31:16] };


        end
      endcase

      default:
      begin
        converted_data = 32'dx;


      end
    endcase
  end
endmodule
