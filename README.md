# DTCore32

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
- ✔️ Meets timing at **100 MHz** on the Arty A7-35t FPGA 
- ✔️ Achieves **210 CoreMark/MHz**  
- ✔️ Displays benchmark results via **UART**  

---

## Future Improvements

- Add support for **RV32M instructions** (multiply/divide)  
- Add support for **external interrupts**  

---


## Files in this Repository

- **/src**  
    RTL files for the CPU system.  

---
## Running RISC-V Formal Tests

This project includes **RISC-V formal verification** support using the [riscv-formal](https://github.com/YosysHQ/riscv-formal.git) framework.  

1. Install the OSS CAD suite from [OSS CAD Suite Build](https://github.com/YosysHQ/oss-cad-suite-build)

2. Clone the riscv-formal GitHub repository:

    ```bash
    git clone https://github.com/YosysHQ/riscv-formal.git
    cd riscv-formal
    ```

3. Clone this repository into the `cores` directory of riscv-formal:

    ```bash
    cd cores
    git clone https://github.com/danthonyt/dtcore32.git
    ```

4. Run the tests:

    ```bash
    make
    ```






