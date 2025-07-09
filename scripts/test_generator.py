# test_generator.py
import utils

import os
import subprocess
from pathlib import Path
import shutil


def write_add_test(num_test_cases):
    """
    Generate the assembly file for the add instruction

    Args:
        num_test_cases (int): number of test cases to generate
    """
    with open("add.S", "w") as f:
        utils.write_start(f)
        test_code = 0
        for i in range(num_test_cases):
            a = utils.rand_32bit_signed()
            b = utils.rand_32bit_signed()
            result = utils.trunc_32bits(a + b)
            f.write(f"# Test Case {test_code}\n")
            f.write(f"  li t0, {utils.to_hex32_str(a)}   # input1\n")
            f.write(f"  li t1, {utils.to_hex32_str(b)}   # input2\n")
            f.write(f"  add t2, t0, t1     # t2 = t0 + t1\n")
            f.write(f"  li t3, {utils.to_hex32_str(result)}  # expected\n")
            f.write(f"  li x11, {utils.to_hex32_str(test_code)}  # expected\n")   # Error code for checking failed test case
            f.write(f"  bne t2, t3, fail\n\n")
            test_code = test_code + 1
        utils.write_end(f)
        # Move asm file to proper location
    shutil.move("add.S", asm_dir / "add.S")

def write_sub_test(num_test_cases):
    """
    Generate the assembly file for the sub instruction

    Args:
        num_test_cases (int): number of test cases to generate
    """
    with open("sub.S", "w") as f:
        utils.write_start(f)
        test_code = 0
        for i in range(num_test_cases):
            a = utils.rand_32bit_signed()
            b = utils.rand_32bit_signed()
            result = utils.trunc_32bits(a - b)
            f.write(f"# Test Case {test_code}\n")
            f.write(f"  li t0, {utils.to_hex32_str(a)}   # input1\n")
            f.write(f"  li t1, {utils.to_hex32_str(b)}   # input2\n")
            f.write(f"  sub t2, t0, t1     # t2 = t0 - t1\n")
            f.write(f"  li t3, {utils.to_hex32_str(result)}  # expected\n")
            f.write(f"  li x11, {utils.to_hex32_str(test_code)}  # expected\n")   # Error code for checking failed test case
            f.write(f"  bne t2, t3, fail\n\n")
            test_code = test_code + 1
        utils.write_end(f)   
        # Move asm file to proper location
    shutil.move("sub.S", asm_dir / "sub.S")
# execution

# Setup paths
working_dir = Path.cwd()
build_dir = working_dir / "build"
asm_dir = build_dir / "asm"
hex_dir = build_dir / "hex"
dump_dir = build_dir / "dump"

# Create necessary directories
build_dir.mkdir(parents=True, exist_ok=True)
asm_dir.mkdir(parents=True, exist_ok=True)
hex_dir.mkdir(parents=True, exist_ok=True)
dump_dir.mkdir(parents=True, exist_ok=True)

write_add_test(16)
write_sub_test(16)

# Process each .S file in the test directory
for asm_file in asm_dir.glob("*.S"):
    base_name = asm_file.stem
    obj_file = asm_file.with_suffix(".o")
    elf_file = asm_file.with_suffix(".v2")
    dump_file = asm_file.with_suffix(".dump")
    bin_file = asm_file.with_suffix(".bin")
    imem_bin = asm_file.with_suffix(".imem.bin")
    dmem_bin = asm_file.with_suffix(".dmem.bin")
    imem_hex = asm_file.with_suffix(".imem.hex")
    dmem_hex = asm_file.with_suffix(".dmem.hex")

    try:
        # Compile and link
        subprocess.run(["riscv32-unknown-elf-gcc", "-c", str(asm_file), "-o", str(obj_file)], check=True)
        subprocess.run(["riscv32-unknown-elf-ld", str(obj_file), "-Ttext", "0x00000000", "-Tdata", "0x00002000", "-o", str(elf_file)], check=True)

        # Generate disassembly
        with open(dump_file, "w") as f:
            subprocess.run(["riscv32-unknown-elf-objdump", "-d", str(elf_file)], stdout=f, check=True)

        # Extract instruction and data segments
        subprocess.run(["riscv32-unknown-elf-objcopy", "-O", "binary", "-j", ".text", str(elf_file), str(imem_bin)], check=True)
        subprocess.run(["riscv32-unknown-elf-objcopy", "-O", "binary", "-j", ".data", str(elf_file), str(dmem_bin)], check=True)

        # Convert to hex with swapped endianness
        def bin_to_swapped_hex(input_file, output_file):
            with open(input_file, "rb") as f_in, open(output_file, "w") as f_out:
                while chunk := f_in.read(4):
                    if len(chunk) < 4:
                        chunk = chunk.ljust(4, b'\x00')
                    swapped = chunk[::-1].hex().upper()
                    f_out.write(swapped + "\n")

        bin_to_swapped_hex(imem_bin, imem_hex)
        bin_to_swapped_hex(dmem_bin, dmem_hex)

        # Move hex files to proper location
        memfile_imem = hex_dir / f"{base_name}_imem.mem"
        memfile_dmem = hex_dir / f"{base_name}_dmem.mem"
        os.rename(imem_hex, memfile_imem)
        os.rename(dmem_hex, memfile_dmem)
        os.rename(dump_file, dump_dir / dump_file.name)

    except subprocess.CalledProcessError as e:
        print(f"Error processing {asm_file}: {e}")
    finally:
        # Clean up
        for f in [obj_file, elf_file, imem_bin, dmem_bin]:
            if f.exists():
                f.unlink()

print(f"All instruction memory .mem files moved to {hex_dir}")
print(f"All data memory .mem files moved to {hex_dir}")
print(f"All dump files moved to {dump_dir}")