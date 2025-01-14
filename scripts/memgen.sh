#!/bin/bash

# Enable extended globbing
shopt -s extglob

# Set directories
WORKINGDIR=$(pwd)
TESTDIR="$HOME/Documents/work/dtcore32/test/riscv-tests/rv32ui"
RVTEST_INCLUDE="$HOME/Documents/work/dtcore32/test/riscv-tests/include"

# Memory and dump directories
MEMDIR="$WORKINGDIR/mem"
HEXDIR="$MEMDIR/hex"
DUMPDIR="$MEMDIR/dump"

#############################################
# Instructions are encoded starting from 0x00000000
# Data memory is encoded starting from 0x00002000

# Ensure the memory directories exist
mkdir -p "$HEXDIR"
mkdir -p "$DUMPDIR"

# Process each assembly file in the test directory
for eachfile in "$TESTDIR"/*.S; do
  if [ -f "$eachfile" ]; then
    # Compile, link, generate dump, and memory hex file
    riscv32-unknown-elf-gcc -c "$eachfile" -I"$RVTEST_INCLUDE" -o "$eachfile.o"
    riscv32-unknown-elf-ld  "$eachfile.o" -Ttext 0x00000000 -Tdata 0x00002000 -o "$eachfile.v2"
    riscv32-unknown-elf-objdump -d "$eachfile.v2" > "$eachfile.dump"
    riscv32-unknown-elf-objcopy -O binary "$eachfile.v2" "$eachfile.bin"


    # Convert binary to hex and swap byte order (change endianness)
hexdump -v -e '4/1 "%02X" "\n"' "$eachfile.bin" | \
awk '{
  swapped = substr($0,7,2) substr($0,5,2) substr($0,3,2) substr($0,1,2);
    print swapped;
}' > "$eachfile.hex"
    # Rename .hex file to .mem
    memfile="$HEXDIR/$(basename "${eachfile%.S}.mem")"
    mv "$eachfile.hex" "$memfile"

    # Move files to the appropriate directories
    mv "$eachfile.dump" "$DUMPDIR/"

    # Clean up intermediate files
    rm -f "$eachfile.o" "$eachfile.v2" "$eachfile.hex" "$eachfile.bin"
  else
    echo "Warning: File \"$eachfile\" does not exist or is not a regular file."
  fi
done

echo "All memory .mem files moved to $HEXDIR."
echo "All dump files moved to $DUMPDIR."
