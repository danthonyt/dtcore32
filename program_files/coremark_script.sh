#!/bin/bash
# build_coremark_mem.sh - Bare-metal CoreMark build script producing IMEM/DMEM .mem files

set -e

# --------------------------
# EDIT THESE DIRECTORIES
# --------------------------

COREMARK_DIR="../coremark"
BAREBONES_DIR="../coremark/barebones"

STARTUP_FILE="startup.S"
LINKER_SCRIPT="link.ld"

IMEM_MEM="cm_imem.mem"
DISASM="coremark.dis"

IMEM_SIZE=65536   # 64 KB IMEM
DMEM_SIZE=65536   # 64 KB DMEM

RISCV_GCC=riscv32-unknown-elf-gcc
OBJCOPY=riscv32-unknown-elf-objcopy
OBJDUMP=riscv32-unknown-elf-objdump

# --------------------------
# SOURCE FILES
# --------------------------

LIBS_SRC=("uart.c" "dtcore_time.c")
COREMARK_SRC=("../coremark/core_main.c" "../coremark/core_list_join.c"  "../coremark/core_matrix.c" "../coremark/core_state.c" "../coremark/core_util.c")
PORT_SRC=("../coremark/barebones/core_portme.c" "../coremark/barebones/ee_printf.c")
ALL_SRC=("$STARTUP_FILE" "${LIBS_SRC[@]}" "${PORT_SRC[@]}" "${COREMARK_SRC[@]}")

ELF="coremark.elf"


riscv32-unknown-elf-gcc -O2 -march=rv32izicsr -mabi=ilp32 -ffreestanding -static -nostdlib -nostartfiles \
    -I"../coremark" -I"../coremark/barebones" -I"." \
    "${ALL_SRC[@]}" -T "$LINKER_SCRIPT" -o "$ELF" -lgcc


# 2. Generate IMEM memory file (Verilog HEX) preserving LMA addresses

IMEM_BIN="imem.bin"
$OBJCOPY -O binary \
    -j .text \
    -j .rodata \
    -j .data \
    -j .sdata \
    $ELF $IMEM_BIN

od -An -t x4 -w4 -v $IMEM_BIN | awk '{print toupper($1)}' > cm_imem.mem


# 6. Generate disassembly
riscv32-unknown-elf-objdump -D \
    -j .text \
    -j .rodata \
    -j .data \
    -j .sdata \
    test.elf > $DISASM


# 7. Cleanup

echo "Build complete!"
echo "  IMEM: $IMEM_MEM ($((IMEM_SIZE/4)) × 32-bit words)"
echo "  DMEM: $DMEM_MEM ($((DMEM_SIZE/4)) × 32-bit words)"
echo "  Disassembly: $DISASM"
