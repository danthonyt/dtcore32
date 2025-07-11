# test_generator.py
import utils
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

utils.create_all_tests(asm_dir)
utils.process_tests(asm_dir, hex_dir, dump_dir)

