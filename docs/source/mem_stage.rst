Data Memory (MEM) Stage
=======================

Overview
--------
The Data Memory (MEM) stage interfaces with the CPU's memory system. It handles both load and store instructions and completes memory operations in a single cycle (subject to memory timing). Responsibilities include:

- Reading from memory for load instructions.
- Writing to memory for store instructions.
- Generating memory traps for misaligned accesses.

Memory Access
-------------
- Memory accesses are **word-aligned**.  
  - Byte and half-word loads are extracted from the corresponding word address.
- For store instructions, the **two least significant bits** of the memory address generate the **byte enable signals** for the memory.

Memory Request Protocol
-----------------------
- At the start of a memory request, the CPU generates a **request valid pulse**.  
- All pipeline stages stall until a **done pulse** is received, indicating the memory operation has completed.

Traps
-----
This stage generates a trap under the following conditions:

- Misaligned load addresses
- Misaligned store addresses

Pipeline Considerations
-----------------------
- The MEM stage receives data and addresses from the EX stage.
- Proper stalling ensures memory operations are completed before subsequent instructions proceed.
