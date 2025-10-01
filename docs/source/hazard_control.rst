Hazard Control
==============
Overview
--------
The hazard control unit manages **stalls**, **forwarding**, and **pipeline flushes** to ensure correct execution in the presence of data and control hazards.

Data Hazards
------------
- **Load-Use Hazard:** Stall occurs if a load instruction in EX is followed by an instruction in ID reading the same register.
- **Memory Request Stall:** Stall occurs if a memory request is active and not complete.

Forwarding
----------
- **EX stage forwarding:** Forward values from MEM or WB to EX if a source register matches a previous instruction's destination.
- **ID stage forwarding:** Forward values from WB to ID if a source register matches WB destination.

Control Hazards & Flushes
-------------------------
- Flush IF/ID, ID/EX, EX/MEM registers for jump/branch mispredicts or trapped instructions.
- Predicted-taken branches may conditionally flush IF/ID to avoid losing instructions when stalled.

Stall Signals
-------------
- **IF/ID Stall:** Triggered by load-use hazard or downstream stall.
- **ID/EX Stall:** Triggered if EX/MEM stage is stalled.
- **EX/MEM Stall:** Triggered by memory request stall or downstream stall.
- **MEM/WB Stall:** Triggered by memory request stall.

Key Signals
-----------
**Match Signals:** Detect register dependencies:

- `id_wb_rs1_match`, `id_wb_rs2_match`
- `id_ex_rs1_match`, `id_ex_rs2_match`
- `ex_mem_rs1_match`, `ex_mem_rs2_match`
- `ex_wb_rs1_match`, `ex_wb_rs2_match`

**Flush Signals:**

- `if_id_flush`, `id_ex_flush`, `ex_mem_flush`, `mem_wb_flush`

**Stall Signals:**

- `if_id_stall`, `id_ex_stall`, `ex_mem_stall`, `mem_wb_stall`
