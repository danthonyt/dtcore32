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

asm_writer.create_all_tests(asm_dir)
asm_writer.process_tests(asm_dir, hex_dir, dump_dir)
cpu_ref = rv32i_reference.rv32i_cpu()
cpu_ref.load_program('addi_imem', hex_dir)
cpu_ref.run(False)

