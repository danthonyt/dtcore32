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
IMEM_MEM="cm_imem.mem"
DMEM_MEM="cm_dmem.mem"
DISASM="coremark.dis"

# Memory sizes (in bytes)
IMEM_SIZE=65536   # 64 KB IMEM
DMEM_SIZE=65536   # 64 KB DMEM

# Cross-compiler
RISCV_GCC=riscv32-unknown-elf-gcc
OBJCOPY=riscv32-unknown-elf-objcopy
OBJDUMP=riscv32-unknown-elf-objdump

# --------------------------
# DO NOT EDIT BELOW THIS LINE
# --------------------------

# Collect all .c files
LIBS_SRC=("uart.c" "trap.c" "dtcore_time.c")
COREMARK_SRC=("../coremark/core_main.c" "../coremark/core_list_join.c"  "../coremark/core_matrix.c" "../coremark/core_state.c" "../coremark/core_util.c")
PORT_SRC=("../coremark/barebones/core_portme.c" "../coremark/barebones/ee_printf.c")
ALL_SRC=("$STARTUP_FILE" "${LIBS_SRC[@]}" "${PORT_SRC[@]}" "${COREMARK_SRC[@]}" )


# Output ELF
ELF="coremark.elf"

# 1. Compile and link
riscv32-unknown-elf-gcc -O2 -march=rv32izicsr -mabi=ilp32 -ffreestanding -static -nostdlib -nostartfiles \
    -I"../coremark" -I"../coremark/barebones" -I"." \
    "${ALL_SRC[@]}" -T "$LINKER_SCRIPT" -o "$ELF" -lgcc
    

# 2. Generate raw binaries
IMEM_BIN="imem.bin"
DMEM_BIN="dmem.bin"

$OBJCOPY -O binary --only-section=.text --only-section=.rodata --only-section=.trap $ELF $IMEM_BIN
$OBJCOPY -O binary --only-section=.data --only-section=.bss $ELF $DMEM_BIN

# 3. Pad binaries to fixed sizes
truncate -s $IMEM_SIZE $IMEM_BIN
truncate -s $DMEM_SIZE $DMEM_BIN

# 4. Delete old mem files if they exist
rm -f $IMEM_MEM $DMEM_MEM

# 5. Convert to 32-bit hex words (one per line, uppercase)
od -An -t x4 -w4 -v $IMEM_BIN | awk '{$1=toupper($1); print $1}' > $IMEM_MEM
od -An -t x4 -w4 -v $DMEM_BIN | awk '{$1=toupper($1); print $1}' > $DMEM_MEM

# 6. Generate disassembly
$OBJDUMP -d $ELF > $DISASM

# 7. Cleanup
rm -f $ELF $IMEM_BIN $DMEM_BIN

echo "Build complete!"
echo "  IMEM: $IMEM_MEM ($((IMEM_SIZE/4)) × 32-bit words)"
echo "  DMEM: $DMEM_MEM ($((DMEM_SIZE/4)) × 32-bit words)"
echo "  Disassembly: $DISASM"
