# test_generator.py
import asm_writer
import rv32i_reference
from pathlib import Path

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


import argparse

def generate_tests():
    print(f"Generating tests")
    asm_writer.create_all_tests(asm_dir)
    asm_writer.process_tests(asm_dir, hex_dir, dump_dir)
    # Your logic here

def run_tests():
    print(f"Running tests")
    cpu_ref = rv32i_reference.rv32i_cpu()
    for test in ["add", "sub", "and", "or", "xor", "sll", "slt", "sltu", "srl", "sra",
                 "addi", "andi", "ori", "xori", "slli", "slti", "sltiu", "srli", "srai",
                 "beq", "bne", "blt", "bge", "bltu", "bgeu", "lui", "auipc", "jal", "jalr",
                 "lb", "lh", "lw", "lbu", "lhu", "sb", "sh", "sw"
                ]:
        cpu_ref.reset()
        is_dmem_load = test in ["lb", "lh", "lw", "lbu", "lhu"]
        cpu_ref.load_program(f'{test}', hex_dir, is_dmem_load)
        cpu_ref.run(False)
        cpu_ref.compare_cpu_regdumps("_dtcore32_regdump.txt","/home/dtorres/Documents/work/dtcore32/build/riscv.sim/sim_1/behav/xsim/", f'{test.upper()}' )

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Test generator and runner")
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--generate", metavar="OUTFILE", help="Generate new tests and save to file")
    group.add_argument("--run", metavar="INFILE", help="Run tests from file")

    args = parser.parse_args()

    if args.generate:
        generate_tests()
    elif args.run:
        run_tests()


