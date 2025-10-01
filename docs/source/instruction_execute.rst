Instruction Execute (EX) Stage
==============================

Overview
--------

The Instruction Execute (EX) stage performs arithmetic, logic, and branch computations. It receives decoded instructions and operands from the Decode stage and computes results for the Memory stage.

Key Functions
-------------

- Perform ALU operations (add, sub, AND, OR, XOR, shifts, etc.)
- Evaluate branch and jump conditions
- Forward results to later pipeline stages to resolve data hazards
- Generate control signals for memory access

Block Diagram
-------------

.. image:: images/ex_stage.png
   :alt: Instruction Execute Stage Block Diagram
   :width: 600px

Signals
-------

- **alu_op** : ALU operation code
- **operand_a** : First ALU input
- **operand_b** : Second ALU input
- **alu_result** : Output from the ALU
- **branch_taken** : Branch decision signal
- **forward_a / forward_b** : Forwarding control signals for hazard resolution

Verilog Example
---------------

.. code-block:: verilog

   module ex_stage(
       input wire clk,
       input wire rst,
       input wire [31:0] operand_a,
       input wire [31:0] operand_b,
       input wire [3:0] alu_op,
       input wire forward_a,
       input wire forward_b,
       output reg [31:0] alu_result,
       output reg branch_taken
   );
       always @(*) begin
           // Simple ALU example
           case (alu_op)
               4'b0000: alu_result = operand_a + operand_b;
               4'b0001: alu_result = operand_a - operand_b;
               4'b0010: alu_result = operand_a & operand_b;
               4'b0011: alu_result = operand_a | operand_b;
               default: alu_result = 32'b0;
           endcase

           // Branch evaluation example
           branch_taken = (alu_result == 0) ? 1'b1 : 1'b0;
       end
   endmodule

Notes
-----

- Forwarding is used to reduce stalls caused by data hazards.
- The ALU control logic is critical for correct execution of instructions.
- Branch decisions in this stage can trigger pipeline flushes if mispredicted.



