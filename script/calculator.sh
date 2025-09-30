#!/bin/bash
set -e

# --------------------------
# EDIT THESE DIRECTORIES
# --------------------------

SRC_SOFTWARE_DIR="../src/software"
SRC_STARTUP_DIR="../src/startup"
BUILD_DIR="../build"

STARTUP_FILE="$SRC_STARTUP_DIR/startup.S"
LINKER_SCRIPT="$SRC_STARTUP_DIR/link.ld"

IMEM_MEM="$BUILD_DIR/calculator.mem"
DISASM="$BUILD_DIR/calculator.dis"

IMEM_SIZE=65536   # 64 KB IMEM
DMEM_SIZE=65536   # 64 KB DMEM

RISCV_GCC=riscv32-unknown-elf-gcc
OBJCOPY=riscv32-unknown-elf-objcopy
OBJDUMP=riscv32-unknown-elf-objdump

# --------------------------
# SOURCE FILES
# --------------------------

ALL_SRC=("$STARTUP_FILE" "$SRC_SOFTWARE_DIR/uart.c" "$SRC_SOFTWARE_DIR/calculator.c")

ELF="$BUILD_DIR/calculator.elf"

# --------------------------
# Ensure build directory exists
# --------------------------

mkdir -p "$BUILD_DIR"

# --------------------------
# Compile ELF
# --------------------------

$RISCV_GCC -O1 -march=rv32izicsr -mabi=ilp32 -ffreestanding -static -nostdlib -nostartfiles \
    "${ALL_SRC[@]}" -T "$LINKER_SCRIPT" -o "$ELF" -lgcc

# --------------------------
# Generate IMEM memory file (Verilog HEX)
# --------------------------

IMEM_BIN="$BUILD_DIR/imem.bin"
$OBJCOPY -O binary \
    -j .text \
    -j .rodata \
    -j .data \
    -j .sdata \
    "$ELF" "$IMEM_BIN"

od -An -t x4 -w4 -v "$IMEM_BIN" | awk '{print toupper($1)}' > "$IMEM_MEM"

# --------------------------
# Generate disassembly
# --------------------------

$OBJDUMP -D \
    -j .text \
    -j .rodata \
    -j .data \
    -j .sdata \
    "$ELF" > "$DISASM"

# --------------------------
# Cleanup / Summary
# --------------------------

echo "Build complete!"
echo "  IMEM: $IMEM_MEM ($((IMEM_SIZE/4)) × 32-bit words)"
echo "  Disassembly: $DISASM"
