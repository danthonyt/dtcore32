#!/bin/bash
set -e

# --------------------------
# EDIT THESE DIRECTORIES
# --------------------------
STARTUP_FILE="startup.S"
LINKER_SCRIPT="link.ld"

IMEM_MEM="hello_world.mem"
DISASM="hello_world.dis"

IMEM_SIZE=65536   # 64 KB IMEM
DMEM_SIZE=65536   # 64 KB DMEM

RISCV_GCC=riscv32-unknown-elf-gcc
OBJCOPY=riscv32-unknown-elf-objcopy
OBJDUMP=riscv32-unknown-elf-objdump

# --------------------------
# SOURCE FILES
# --------------------------

ALL_SRC=("startup.S" "uart.c" "hello_world.c")

ELF="hello_world.elf"


riscv32-unknown-elf-gcc -O1 -march=rv32izicsr -mabi=ilp32 -ffreestanding -static -nostdlib -nostartfiles \
    "${ALL_SRC[@]}" -T "$LINKER_SCRIPT" -o "$ELF" -lgcc


# 2. Generate IMEM memory file (Verilog HEX) preserving LMA addresses

IMEM_BIN="imem.bin"
$OBJCOPY -O binary \
    -j .text \
    -j .rodata \
    -j .data \
    -j .sdata \
    $ELF $IMEM_BIN

od -An -t x4 -w4 -v $IMEM_BIN | awk '{print toupper($1)}' > $IMEM_MEM


# 6. Generate disassembly
riscv32-unknown-elf-objdump -D \
    -j .text \
    -j .rodata \
    -j .data \
    -j .sdata \
    $ELF > $DISASM


# 7. Cleanup

echo "Build complete!"
echo "  IMEM: $IMEM_MEM ($((IMEM_SIZE/4)) × 32-bit words)"
echo "  Disassembly: $DISASM"
