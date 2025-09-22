#!/bin/bash
set -e

IMEM_BIN=imem.bin
DMEM_BIN=dmem.bin
IMEM_MEM=hello_world_imem.mem
DMEM_MEM=hello_world_dmem.mem

# 1. Compile and link (with startup)
riscv32-unknown-elf-gcc -march=rv32izicsr -mabi=ilp32 -nostdlib -nostartfiles \
    -Wl,-T,link.ld -o hello_world.elf startup.S uart.c hello_world.c trap.c -lgcc

# 2. Generate raw binaries
# IMEM: just .text
riscv32-unknown-elf-objcopy -O binary --only-section=.text \
 --only-section=.rodata --only-section=.trap hello_world.elf $IMEM_BIN

# DMEM: data, rodata, bss (allocate .bss as zeros)
riscv32-unknown-elf-objcopy -O binary \
    --only-section=.data --only-section=.bss \
    hello_world.elf $DMEM_BIN

# 3. Pad binaries to match IMEM/DMEM sizes (64 KB)
truncate -s 65536 $IMEM_BIN
truncate -s 65536 $DMEM_BIN

# 4. Convert to 32-bit hex words, one per line
# IMEM
od -An -t x4 -w4 -v $IMEM_BIN | awk '{$1=toupper($1); print $1}' > $IMEM_MEM

# DMEM
od -An -t x4 -w4 -v $DMEM_BIN | awk '{$1=toupper($1); print $1}' > $DMEM_MEM

# 5. Generate disassembly including .text and .rodata
{
    echo "Disassembly of .text and .rodata:"
    riscv32-unknown-elf-objdump -D --section=.text hello_world.elf
    riscv32-unknown-elf-objdump -s --section=.rodata hello_world.elf
} > hello_world.dis

# 6. Cleanup: keep only .mem and .dis
rm -f hello_world.elf $IMEM_BIN $DMEM_BIN

echo "Build complete!"
echo "  IMEM: $IMEM_MEM (16384 × 32-bit words)"
echo "  DMEM: $DMEM_MEM (16384 × 32-bit words)"
echo "  Disassembly: hello_world.dis"
