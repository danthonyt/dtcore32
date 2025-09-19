#!/bin/bash
# build_coremark_mem.sh - Bare-metal CoreMark build script producing IMEM/DMEM .mem files

set -e

# --------------------------
# EDIT THESE DIRECTORIES
# --------------------------

# CoreMark sources (unmodified)
COREMARK_DIR="../coremark"

# Barebones port sources (modified)
BAREBONES_DIR="../coremark/barebones"

# Startup and linker
STARTUP_FILE="startup.S"
LINKER_SCRIPT="link.ld"

# Output files
IMEM_MEM="imem.mem"
DMEM_MEM="dmem.mem"
DISASM="coremark.dis"

# Memory sizes (in bytes)
IMEM_SIZE=65536   # 10 KB IMEM
DMEM_SIZE=65536   # 10 KB DMEM

# Cross-compiler
RISCV_GCC=riscv32-unknown-elf-gcc
OBJCOPY=riscv32-unknown-elf-objcopy
OBJDUMP=riscv32-unknown-elf-objdump

# --------------------------
# DO NOT EDIT BELOW THIS LINE
# --------------------------

# Collect all .c files
COREMARK_SRC=($(find "$COREMARK_DIR" -maxdepth 1 -name "*.c"))
PORT_SRC=($(find "$BAREBONES_DIR" -maxdepth 1 -name "*.c"))

# Output ELF
ELF="coremark.elf"

# 1. Compile and link
$RISCV_GCC -O2 -march=rv32i -mabi=ilp32 -nostartfiles -ffreestanding -static \
    -I"$COREMARK_DIR" -I"$BAREBONES_DIR" \
    "$STARTUP_FILE" \
    "${COREMARK_SRC[@]}" "${PORT_SRC[@]}" \
    -T "$LINKER_SCRIPT" -o $ELF




# 2. Generate raw binaries
# IMEM: only .text
IMEM_BIN="imem.bin"
$OBJCOPY -O binary --only-section=.text $ELF $IMEM_BIN

# DMEM: .data + .rodata + .bss
DMEM_BIN="dmem.bin"
$OBJCOPY -O binary --only-section=.data --only-section=.rodata --only-section=.bss $ELF $DMEM_BIN

# 3. Pad binaries to fixed sizes
truncate -s $IMEM_SIZE $IMEM_BIN
truncate -s $DMEM_SIZE $DMEM_BIN

# 4. Convert to 32-bit hex words (one per line, uppercase)
od -An -t x4 -w4 -v $IMEM_BIN | awk '{$1=toupper($1); print $1}' > $IMEM_MEM
od -An -t x4 -w4 -v $DMEM_BIN | awk '{$1=toupper($1); print $1}' > $DMEM_MEM

# 5. Generate disassembly
$OBJDUMP -d $ELF > $DISASM

# 6. Cleanup
rm -f $ELF $IMEM_BIN $DMEM_BIN

echo "Build complete!"
echo "  IMEM: $IMEM_MEM ($((IMEM_SIZE/4)) × 32-bit words)"
echo "  DMEM: $DMEM_MEM ($((DMEM_SIZE/4)) × 32-bit words)"
echo "  Disassembly: $DISASM"
