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
- ✔️ Meets timing at **100 MHz** on the Arty A7-35t FPGA 
- ✔️ Achieves **210 CoreMark/MHz**  
- ✔️ Displays benchmark results via **UART**  

---

## Future Improvements

- Add support for **RV32M instructions** (multiply/divide)  
- Add support for **external interrupts**  

---


## Files in this Repository

- **/coremark**  
  Port files for running the CoreMark benchmark on the core.

- **/peripherals**  
  RTL code for peripherals to be used with the CPU.

- **/scripts**  
  Script files to generate memory files (ROM/IMEM) for FPGA simulations.

- **/sim**  
  SystemVerilog testbench for simulating the CPU core.

- **/src**  
  - **/constr**  
    Constraint file for the Arty A7 FPGA. For other boards, a new constraint file will need to be created.  
  - **/soc**  
    RTL files for the CPU system.  
  - **/software**  
    C source files for generating programs, including UART and timer support.  
  - **/startup**  
    Linker script and startup assembly file used for memory file generation.

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

---

### Running CoreMark on the RISC-V Core

1. **Install the RISC-V GNU Toolchain**
   - Make sure you have a RISC-V compiler installed. The provided `coremark.sh` script assumes the **riscv32-unknown-elf** toolchain.
   - You can install it from https://github.com/riscv-collab/riscv-gnu-toolchain.

2. **Prepare the project**
   - Run the `coremark.sh` script to generate a memory initialization file (e.g., `.mem`) for your target memory.
   - Provide a pin constraints file for your board.
   - initialize submodules with git submodule update --init --recursive


3. **Generate the bitstream**
   - Use your preferred synthesis tool to build the project and program your board.






