#!/bin/bash
set -e

SRC=hello.c
ELF=hello.elf
IMEM_BIN=imem.bin
DMEM_BIN=dmem.bin
IMEM_HEX=imem.hex
DMEM_HEX=dmem.hex
DISASM=hello.dis
LINKER_SCRIPT=link.ld

# 1. Compile and link
riscv32-unknown-elf-gcc -march=rv32i -mabi=ilp32 -nostdlib \
    -Wl,-T,$LINKER_SCRIPT -o $ELF $SRC

# 2. Generate raw binary files for IMEM and DMEM
riscv32-unknown-elf-objcopy -O binary --only-section=.text $ELF $IMEM_BIN
riscv32-unknown-elf-objcopy -O binary --only-section=.data --only-section=.rodata --only-section=.bss $ELF $DMEM_BIN

# 3. Convert binaries to 32-bit hex words, one per line
# IMEM
od -An -t x4 -w4 -v $IMEM_BIN | awk '{$1=toupper($1); print $1}' > $IMEM_HEX

# DMEM
od -An -t x4 -w4 -v $DMEM_BIN | awk '{$1=toupper($1); print $1}' > $DMEM_HEX

# 4. Generate disassembly
riscv32-unknown-elf-objdump -d $ELF > $DISASM

echo "Build complete!"
echo "  IMEM: $IMEM_HEX (256 × 32-bit words)"
echo "  DMEM: $DMEM_HEX (256 × 32-bit words)"
echo "  Disassembly: $DISASM"
