#!/bin/bash
set -e

SRC=hello.c
STARTUP=startup.S
ELF=hello.elf
IMEM_BIN=imem.bin
DMEM_BIN=dmem.bin
IMEM_MEM=imem.mem
DMEM_MEM=dmem.mem
DISASM=hello.dis
LINKER_SCRIPT=link.ld

# 1. Compile and link (with startup)
riscv32-unknown-elf-gcc -march=rv32i -mabi=ilp32 -nostdlib -nostartfiles \
    -Wl,-T,$LINKER_SCRIPT -o $ELF $STARTUP $SRC -lgcc


# 2. Generate raw binaries
# IMEM: just .text
riscv32-unknown-elf-objcopy -O binary --only-section=.text $ELF $IMEM_BIN

# DMEM: data, rodata, bss (allocate .bss as zeros)
riscv32-unknown-elf-objcopy -O binary \
    --only-section=.data --only-section=.rodata --only-section=.bss \
    $ELF $DMEM_BIN

# 3. Pad binaries to match IMEM/DMEM sizes (1 KB = 256 words)
truncate -s 10240 $IMEM_BIN
truncate -s 10240 $DMEM_BIN

# 4. Convert to 32-bit hex words, one per line
# IMEM
od -An -t x4 -w4 -v $IMEM_BIN | awk '{$1=toupper($1); print $1}' > $IMEM_MEM

# DMEM
od -An -t x4 -w4 -v $DMEM_BIN | awk '{$1=toupper($1); print $1}' > $DMEM_MEM

# 5. Generate disassembly
riscv32-unknown-elf-objdump -d $ELF > $DISASM

# 6. Cleanup: keep only .mem and .dis
rm -f $ELF $IMEM_BIN $DMEM_BIN

echo "Build complete!"
echo "  IMEM: $IMEM_MEM (2560 × 32-bit words)"
echo "  DMEM: $DMEM_MEM (2560 × 32-bit words)"
echo "  Disassembly: $DISASM"
