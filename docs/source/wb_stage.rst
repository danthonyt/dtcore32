Write Back (WB) Stage
=====================

Overview
--------
The Write Back (WB) stage is responsible for committing instruction results to the CPU state. It handles:

- Writing results to the **register file**.
- Updating **Control and Status Registers (CSRs)** if required by the instruction.
- Committing **trapped instructions**, which redirects the PC to the trap handler.

Operations
----------
- **Register Writes:** Writes ALU or memory results to the destination register.
- **CSR Updates:** Writes to CSR registers as specified by CSR instructions.
- **Trap Handling:** On a trap, the instruction is committed and the PC is set to the appropriate trap vector.

Pipeline Considerations
-----------------------
- The WB stage receives its inputs from the MEM or EX stage, depending on the instruction type.
- Proper sequencing ensures that register updates and trap handling occur **after memory accesses** and **ALU operations** complete.
