Instruction Fetch (IF) Stage
============================

Overview
--------

The Instruction Fetch (IF) stage is responsible for retrieving instructions from memory. It determines the next instruction address and passes the instruction to the Decode stage.

Key Functions
-------------

- Fetch the instruction from instruction memory based on the Program Counter (PC)
- Increment or update the PC depending on branch/jump outcomes
- Handle pipeline stalls and flushes if required

Block Diagram
-------------

.. image:: images/if_stage.png
   :alt: Instruction Fetch Stage Block Diagram
   :width: 600px

Signals
-------

- **pc** : Current program counter
- **instr** : Instruction output
- **pc_next** : Next program counter value
- **stall** : Pipeline stall signal
- **flush** : Pipeline flush signal

Verilog Example
---------------

.. code-block:: verilog

   module if_stage(
       input wire clk,
       input wire rst,
       input wire [31:0] pc_in,
       input wire stall,
       input wire flush,
       output reg [31:0] pc_out,
       output reg [31:0] instr_out
   );
       always @(posedge clk or posedge rst) begin
           if (rst) begin
               pc_out <= 32'b0;
           end else if (flush) begin
               pc_out <= pc_in; // flush pipeline
           end else if (!stall) begin
               pc_out <= pc_in + 4; // fetch next instruction
           end
       end
   endmodule

Notes
-----

- The IF stage is critical for pipeline performance.
- Proper handling of stalls and flushes prevents hazards in subsequent stages.

