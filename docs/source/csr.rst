Control and Status Registers (CSR)
==================================

Overview
--------
The CPU implements a subset of the **machine-level CSRs** from the RV32I/RV64I specification. These registers are used for exception handling, performance counters, and temporary storage during traps.

Supported CSRs
--------------

**Trap and Exception Registers:**

- `mtvec`    : Machine trap-vector base address
- `mscratch` : Temporary register for machine trap handling
- `mepc`     : Machine exception program counter
- `mcause`   : Cause of the last exception
- `mtval`    : Exception-specific value (faulting address or instruction)

**Performance Counters:**

- `mcycle`     : Counts the number of clock cycles
- `minstret`   : Counts the number of instructions retired

Operations
----------
- CSR instructions **read** values during the **Instruction Decode (ID)** stage.
- CSR **writes** are committed during the **Write Back (WB)** stage.
- Trap instructions update `mepc`, `mcause`, `mtval`, and optionally other CSRs.
- `mcycle` and `minstret` are incremented automatically on each cycle or instruction retirement.
- **Unsupported CSR addresses** return `0` when read.
