#!/bin/bash
# build_coremark_mem.sh - Bare-metal CoreMark build script producing IMEM/DMEM .mem files

set -e

# --------------------------
# EDIT THESE DIRECTORIES
# --------------------------

COREMARK_DIR="../coremark"
BAREBONES_DIR="../coremark/barebones"
SRC_SOFTWARE_DIR="../src/software"
SRC_STARTUP_DIR="../src/startup"
BUILD_DIR="../build"

STARTUP_FILE="$SRC_STARTUP_DIR/startup.S"
LINKER_SCRIPT="$SRC_STARTUP_DIR/link.ld"

IMEM_MEM="$BUILD_DIR/coremark_program.mem"
DISASM="$BUILD_DIR/coremark.dis"

IMEM_SIZE=65536   # 64 KB IMEM
DMEM_SIZE=65536   # 64 KB DMEM

RISCV_GCC=riscv32-unknown-elf-gcc
OBJCOPY=riscv32-unknown-elf-objcopy
OBJDUMP=riscv32-unknown-elf-objdump

# --------------------------
# SOURCE FILES
# --------------------------

# Non-CoreMark software files from src/software
LIBS_SRC=("$SRC_SOFTWARE_DIR/uart.c" "$SRC_SOFTWARE_DIR/dtcore_time.c")

COREMARK_SRC=("$COREMARK_DIR/core_main.c" "$COREMARK_DIR/core_list_join.c" \
  "$COREMARK_DIR/core_matrix.c" "$COREMARK_DIR/core_state.c" "$COREMARK_DIR/core_util.c")

PORT_SRC=("$BAREBONES_DIR/core_portme.c" "$BAREBONES_DIR/ee_printf.c")

ALL_SRC=("$STARTUP_FILE" "${LIBS_SRC[@]}" "${PORT_SRC[@]}" "${COREMARK_SRC[@]}")

ELF="$BUILD_DIR/coremark.elf"

# --------------------------
# Ensure build directory exists
# --------------------------

mkdir -p "$BUILD_DIR"

# --------------------------
# Compile ELF
# --------------------------

$RISCV_GCC -O2 -march=rv32izicsr -mabi=ilp32 -ffreestanding -static -nostdlib -nostartfiles \
    -I"$COREMARK_DIR" -I"$BAREBONES_DIR" -I"$SRC_SOFTWARE_DIR" \
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
echo "  DMEM: $DMEM_MEM ($((DMEM_SIZE/4)) × 32-bit words)"
echo "  Disassembly: $DISASM"
