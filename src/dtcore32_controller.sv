module dtcore32_controller(
   input logic clk,rst,
    input logic [6:0]  op,
    input logic [2:0]  funct3,
    input logic funct7b5,
    output logic [1:0]  ID_result_src,ID_alu_a_src,ID_mem_wr,
    output logic [3:0]  ALUControlD,
    output logic [2:0]  ID_imm_src,ID_load_size,
    output logic ID_alu_b_src,  ID_reg_wr, ID_jump, ID_branch,ID_pc_target_alu_src,
    output logic isNop,
    output logic is_unknown_instruction
  );

// ===========================================================================
// 			          Parameters, Registers, and Wires
// ===========================================================================

// ===========================================================================
// 			          Instantiations
// ===========================================================================

// ===========================================================================
// 			          Implementation
// ===========================================================================
  logic [1:0] ALUOp;
  logic  [18:0] controls;
  logic RtypeSub,ItypeSub;
  logic isNop_sig,opcode_exception, ALUOp_exception;
  logic [3:0] ALUControlD_sig;
  assign RtypeSub = op[5] & funct7b5;
  assign ItypeSub = ~op[5] & funct7b5;
  assign {ID_reg_wr, ID_imm_src, ID_alu_a_src, ID_alu_b_src,ID_mem_wr, ID_result_src, ID_branch, ALUOp, ID_jump, ID_load_size,ID_pc_target_alu_src} = controls;
  // nop handling
  assign isNop = isNop_sig;
  assign ALUControlD = isNop_sig ? 0 : ALUControlD_sig;
  // exception handling
  always_ff @(posedge clk)begin
    if (rst)
    is_unknown_instruction <=0;
    else 
    is_unknown_instruction <= opcode_exception | ALUOp_exception;
  end
  always_comb
  begin
    isNop_sig = 0;
    opcode_exception = 0;
    case (op)
      7'b0000011:
      case(funct3)
        3'b000:
          controls = 19'b1_000_00_1_00_01_0_00_0_001_0;	//lb
        3'b001:
          controls = 19'b1_000_00_1_00_01_0_00_0_011_0;	//lh
        3'b010:
          controls = 19'b1_000_00_1_00_01_0_00_0_000_0;	//lw
        3'b100:
          controls = 19'b1_000_00_1_00_01_0_00_0_010_0;	//lbu
        3'b101:
          controls = 19'b1_000_00_1_00_01_0_00_0_100_0;	//lhu
        default:
        begin
          controls = 0;	//unknown instruction
          opcode_exception = 1;
        end
      endcase
      // FENCE,ECALL, and EBREAK should be a NOP for now
      //FENCE, ECALL and EBREAK and zicsr
      
      7'b00001111:
      begin
        isNop_sig = 1;
        controls = 19'b1_000_00_1_00_00_0_10_0_000_0;	//addi x0,x0,0
      end
      // zicsr instruction
      7'b1110011:
      case (funct3)
      // CSRRW
      3'b001: 
      // CSRRS
      3'b010:
      // CSRRC
      3'b011:
      // CSRRWI
      3'b101:
      // CSRRSI
      3'b110:
      // CSRRCI
      3'b111:
        default: 
      endcase

      7'b0100011:
      case(funct3)
        3'b000:
          controls = 19'b0_001_00_1_11_00_0_00_0_000_0;	//sb
        3'b001:
          controls = 19'b0_001_00_1_10_00_0_00_0_000_0;	//sh
        3'b010:
          controls = 19'b0_001_00_1_01_00_0_00_0_000_0;	//sw
        default:
        begin
          controls = 0;	//unknown instruction
          opcode_exception = 1;
        end
      endcase
      7'b0110011:
        controls = 19'b1_000_00_0_00_00_0_10_0_000_0;	//R-type
      7'b1100011:
        controls = 19'b0_010_00_0_00_00_1_01_0_000_0;	//beq
      //I-type ALU or shift
      7'b0010011:
      case (funct3)
        3'b000,3'b010,3'b011,3'b100,3'b110,3'b111:
          controls = 19'b1_000_00_1_00_00_0_10_0_000_0;	//I-type ALU
        3'b001,3'b101:
          controls = 19'b1_100_00_1_00_00_0_10_0_000_0;	//I-type Shift
        default:
        begin
          controls = 0;	//unknown instruction
          opcode_exception = 1;
        end
      endcase											//I-type shift
      7'b1101111:
        controls = 19'b1_011_00_0_00_10_0_00_1_000_0;  //jal
      7'b0110111:
        controls = 19'b1_101_01_1_00_00_0_00_0_000_0;  //U-type lui
      7'b0010111:
        controls = 19'b1_101_10_1_00_00_0_00_0_000_0; //U-type auipc
      7'b1100111:
        controls = 19'b1_000_00_1_00_10_0_00_1_000_1; //jalr
      7'b0000000:
        controls = 19'b0_000_00_0_00_00_0_00_0_000_0;	//reset
      default:
      begin
        controls = 0;	//unknown instruction
        opcode_exception = 1;
      end

    endcase

  end

  always_comb
  begin
    ALUOp_exception = 0;
    case (ALUOp)
      //I-type Load, S-type, U-type
      2'b00:
        ALUControlD_sig = 4'b0000; //add- lw,sw,lb,lh,lbu,lhu,sb,sh,auipc,lui
      //B-type
      2'b01:
      case (funct3)
        3'b000:
          ALUControlD_sig = 4'b0001; //sub - beq
        3'b001:
          ALUControlD_sig = 4'b1100; //sub - bne
        3'b100:
          ALUControlD_sig = 4'b0101; //blt
        3'b101:
          ALUControlD_sig = 4'b1010; //bge
        3'b110:
          ALUControlD_sig = 4'b0110; //bltu
        3'b111:
          ALUControlD_sig = 4'b1011; //bgeu

        default:
        begin
          ALUControlD_sig = 0; //unknown
          ALUOp_exception = 1;
        end

      endcase
      //R-type, I-type ALU,I-type logical shift
      2'b10:
      case (funct3)
        3'b000:
          if (RtypeSub)
            ALUControlD_sig = 4'b0001; //sub
          else
            ALUControlD_sig = 4'b0000; //add

        3'b001:
          ALUControlD_sig = 4'b0100; //sll
        3'b010:
          ALUControlD_sig = 4'b0101; //slt
        3'b011:
          ALUControlD_sig = 4'b0110; //sltu
        3'b100:
          ALUControlD_sig = 4'b0111; //xor
        3'b101:
          if (RtypeSub || ItypeSub)
            ALUControlD_sig = 4'b1000; //sra
          else
            ALUControlD_sig = 4'b1001; //srl
        3'b110:
          ALUControlD_sig = 4'b0011; //or
        3'b111:
          ALUControlD_sig = 4'b0010; //and
        default:
        begin
          ALUControlD_sig = 0; //unknown
          ALUOp_exception = 1;
        end
      endcase
      default:
      begin
        ALUControlD_sig = 0; //unknown
        ALUOp_exception = 1;
      end
    endcase
  end
endmodule



