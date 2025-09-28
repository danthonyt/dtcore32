# DTCore32

**Documentation:** [LINK]

DTCore32 is a **5-stage pipelined RISC-V CPU core** implemented in Verilog that supports the **RV32I ISA (version 2.2)**.  
It features a **gshare branch predictor** to reduce branch penalties and has **partial machine-mode support**, handling exceptions through the CSR system (external interrupts not yet implemented).  
The core has been successfully deployed on **FPGA** and benchmarked using **CoreMark**, achieving **210 CoreMark/MHz** with results displayed through UART.

---

## Goals

- ✅ Become familiar with **formal verification**  
- ✅ Get the core to **pass riscv-formal**  
- ✅ Implement **UART output** for program results  
- ✅ Benchmark the core using **CoreMark**  

---

## Pipeline Stages

- **Instruction Fetch (IF)** – Fetches instructions from memory, updates the program counter (PC).  
- **Instruction Decode (ID)** – Decodes instruction, reads registers, generates control signals, and includes a **gshare branch predictor** to reduce stalls.  
- **Execute (EX)** – Performs ALU operations and calculates branch targets.  
- **Memory (MEM)** – Handles load/store instructions through data memory.  
- **Writeback (WB)** – Writes results back into the register file or CSR file.  

---

## Current Status

- ✔️ Passes **riscv-formal** verification  
- ✔️ Meets timing at **100 MHz** on FPGA  
- ✔️ Achieves **210 CoreMark/MHz**  
- ✔️ Displays benchmark results via **UART**  

---

## Future Improvements

- Add support for **RV32M instructions** (multiply/divide)  
- Add support for **external interrupts**  

---


## Files in this repository
/sim
  systemverilog testbench for the core
/rtl
  rtl code for the riscv core, as well as rtl for the bram and bus, for communication to peripherals. Utilizes an Axi Lite 
  master to communicate with peripherals, in this case the UART.
/peripherals
  rtl code for peripherals to be used with the core. as of now, only contains a UART axi lite slave.
/program_files
  files related to generating a a .mem file for generating the ROM used by the core, as well as startup code and a linker 
  script for setting up the program

---


