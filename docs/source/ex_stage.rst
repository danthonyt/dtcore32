Instruction Execute (EX) Stage
==============================

Overview
--------
The Instruction Execute (EX) stage performs all computations required by the instruction. It completes in a single cycle and is responsible for:

- Executing arithmetic and logical operations.
- Calculating branch conditions.
- Computing memory addresses for load and store instructions.
- Generating traps for misaligned addresses.

Supported Operations
--------------------
The EX stage implements all standard RV32I instructions. Key operations include:

**Arithmetic & Logical Operations:**

- ADD, SUB
- AND, OR, XOR
- LEFT SHIFT, RIGHT SHIFT (logical and arithmetic)

**Relational / Branch Operations:**

- BEQ, BNE
- BLT, BGE, BLTU, BGEU

**Address Calculations:**

- Computes relative or absolute addresses for jump, branch, load, and store instructions.
- Instruction and memory addresses are word-aligned; misaligned accesses generate traps.

Traps
-----
The EX stage generates a trap in the following cases:

- Misaligned instruction addresses

Pipeline Considerations
-----------------------
- The EX stage receives operands from the ID stage.
- Results are forwarded to subsequent stages or used for branch evaluation.
- Proper handling of stalls and flushes ensures correct execution of dependent instructions.

Notes
-----
Even though the core implements the full RV32I instruction set, this section highlights the operations directly handled by the EX stage.




