# dtcore32 - A 5-Stage Pipelined RV32I CPU Core in Verilog

**dtcore32** is a RISC-V CPU core implementing the **RV32I** base instruction set architecture with a classic **5-stage pipeline**, written from scratch in Verilog. It passes timing with a maximum frequency of approximately 333 MHz on the Artix A7-35t FPGA.

![RISC-V](https://img.shields.io/badge/RISC--V-RV32I-blue) ![Pipeline](https://img.shields.io/badge/Pipeline-5--Stage-success) ![Language](https://img.shields.io/badge/Language-Verilog-orange)

---

## Pipeline Stages


- **IF (Instruction Fetch):** Fetches instruction from instruction memory.
- **ID (Instruction Decode):** Decodes the instruction, reads registers.
- **EX (Execute):** Performs ALU operations, calculates branches.
- **MEM (Memory):** Accesses data memory for loads/stores.
- **WB (Write Back):** Writes results back to the register file.

---

## Hazard Detection

Hazard detection is crucial to ensured that intstructions are executed correctly in the 5-stage pipeline. If either source 
register being written to in the previous instruction matches the read register in a subsequent one, that new value must be forwarded 
so that the old value is not used. This is called a RAW (read-after-write) data hazard. Another data hazard is when a load instruction is
in the execute stage, while another instruction's source register matches the destination register of the load is in the decode stage. In this case, the pipeline must be stalled.

Another type of data hazard is a control hazard. This occurs when pipelines do not know the outcome of a branch, in this immplementation, 
the branch is always assumed to be taken. In the event the branch is found to be not taken, the erroneous instructions will be flushed, and 
the proper branch will then be taken.

---

## Testing

Testing was done using riscv-tests. This is a github repository containing assembly unit tests for the RV32I instruction set. 
Passes testing for the rv32ui test virtual machine.

---

## Features

- Full **RV32I** instruction set (no compressed or extensions yet)
- **5-stage pipeline** with clean stage separation
- Support for **branch and jump instructions**
- Separate instruction and data memory (Harvard architecture)
- Compatible with **RISC-V GCC toolchain**
- Modular, readable, and commented Verilog
- Easily extendable for future ISA features (RV32M, CSRs, interrupts, etc.)

---

## 🚀 Getting Started

### Install the riscv-gnu-toolchain
https://github.com/riscv-collab/riscv-gnu-toolchain
choose the rv32i architecture
version 2.2
make sure PATH/TO/INSTALL/bin is added to PATH

## Install riscv-test
set the RISCV environment variable to PATH/TO/INSTALL
https://github.com/riscv-software-src/riscv-tests?tab=readme-ov-file


### Clone the repo

```bash
git clone https://github.com/yourusername/dtcore32.git
cd dtcore32
