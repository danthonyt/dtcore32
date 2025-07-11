# utils.py
import random
import os
import subprocess
import random
from pathlib import Path
import shutil

class AsmWriter:
    def __init__(self, file_handle, asm_dir, start_address=0x0):
        self.f = file_handle
        self.asm_dir = asm_dir
        self.pc = start_address
        self.labels = {}
        # all 32 registers
        self.registers = [f"x{i}" for i in range(32)]

        # exclude x0 from dest reg selection
        self.dest_registers = [f"x{i}" for i in range(1,32)]

        self.named_regs = {
            "zero": "x0",
            "ra": "x1",
            "sp": "x2",
            "gp": "x3",
            "tp": "x4",
            "t0": "x5",
            "t1": "x6",
            "t2": "x7",
            "s0": "x8",
            "s1": "x9",
            "a0": "x10",
            "a1": "x11",
            "a2": "x12",
            "a3": "x13",
            "a4": "x14",
            "a5": "x15",
            "a6": "x16",
            "a7": "x17",
            "s2": "x18",
            "s3": "x19",
            "s4": "x20",
            "s5": "x21",
            "s6": "x22",
            "s7": "x23",
            "s8": "x24",
            "s9": "x25",
            "s10": "x26",
            "s11": "x27",
            "t3": "x28",
            "t4": "x29",
            "t5": "x30",
            "t6": "x31"
        }

    def write_instr(self, line):
        """Write a real instruction and increment PC."""
        self.f.write(line + "\n")
        self.pc += 4

    def write_directive(self, line):
        """Write assembler directive (like .text, .globl) — does NOT increment PC."""
        self.f.write(line + "\n")

    def label(self, name):
        """Write a label and register its address — does NOT increment PC."""
        self.labels[name] = self.pc
        self.f.write(f"{name}:\n")

    def comment(self, text):
        """Write a comment."""
        self.f.write(f"# {text}\n")

    def current_pc(self):
        return self.pc

    def get_label_address(self, name):
        return self.labels.get(name, None)
    
    def write_test_start(self):
        """
        Initialize all registers to zero for the start of each test
        """
        self.write_directive(".section .text")
        self.write_directive(".global _start")
        self.write_directive(".global norelax")
        self.write_directive(".global norvc")
        self.label("_start")
        # reset all registers to 0 at the start of the test
        for name in self.dest_registers:
            self.write_instr(f"addi {name}, x0, 0")

    def write_test_end(self):
        """
        Generate the pass and fail loops at the end of an assembly test
        """
        # pass and fail codes and loop forever
        self.label("pass")
        self.write_instr("addi a0, x0, 0")
        self.write_instr("addi a7, x0, 93")
        self.write_instr("addi gp, x0, 1")
        self.write_instr("ecall")
        self.write_instr("j pass")
        self.label("fail")
        self.write_instr("addi a0, x0, 0")
        self.write_instr("addi a7, x0, 93")
        self.write_instr("addi gp, x0, 0")
        self.write_instr("ecall")
        self.write_instr("j fail")

    def test_write_check_eq(self, reg1, reg2):
        for reg in {reg1, reg2}:
            if reg not in self.named_regs:
                raise ValueError(f"Invalid register: '{reg}'")
        self.write_instr(f"bne {reg1}, {reg2}, fail")

    def emit_li(self, rd, value):
        """
        Emit RISC-V instructions to load a 32-bit immediate into register rd.

        Args:
            rd (str): destination register name, e.g. 't0'
            value (int): 32-bit signed integer value to load
            write_instr (func): function to write a single instruction line, e.g. write_instr(str)
        """

        # Add 0x800 to value to properly round for sign-extended lower 12 bits
        upper = ((value + 0x800) >> 12) & 0xF_FFFF  
        lower = value & 0xFFF

        # Sign-extend lower 12 bits
        if lower >= 0x800:
            lower -= 0x1000

        # Emit instructions
        self.write_instr(f"lui {rd}, {upper}")
        self.write_instr(f"addi {rd}, {rd}, {lower}")

    def to_hex32_str(self, val):
        """
        Converts value to a 32 bit hex string
        Args:
            val: the value to convert to a 32 bit hex string
        Returns:
            str: the 32 bit hex string
        """
        return f"0x{val & 0xFFFF_FFFF:08x}"
    
    def gen_r_itype_test(self, instr_name, operator_func, num_test_cases, is_immediate=False, is_shift=False):
        """
        Generate the assembly file for an R-type or I-type instruction (add, sub, or, etc.)

        Args:
            instr_name (str): The RISC-V instruction name (e.g., 'add', 'sub', 'or')
            operator_func (function): Function that takes two ints and returns the result
            num_test_cases (int): Number of test cases to generate
            is_immediate (bool): indicates whether or not the instruction uses immediates
            is_shift (bool): indicates whether or not the instruction is a shift instruction
        """
        self.write_test_start()
        for test_case_number in range(num_test_cases):
            a = self.rand_nbit(32, True)
            self.comment(f"test case {test_case_number}")
            self.emit_li("t0", a) # input 1

            if is_immediate:
                # generate random 12-bit signed immediate
                imm = self.rand_nbit(12, True)
                if is_shift:
                    imm = imm & 0x1F
                expected_value = self.trunc_32bits(operator_func(a, imm))
                self.write_instr(f"{instr_name} t2, t0, {imm}")
            else:
                b = self.rand_nbit(32, True)
                expected_value = self.trunc_32bits(operator_func(a, b))
                self.emit_li("t1", b) # input 2
                self.write_instr(f"{instr_name} t2, t0, t1")

            self.emit_li("t3", expected_value) # expected value
            self.emit_li("a1", test_case_number) # test case id
            self.test_write_check_eq("t2", "t3")
        self.write_test_end()
        filename = f"{instr_name}.S"
        shutil.move(filename, self.asm_dir / filename)

    def gen_btype_test(self, instr_name, condition_func, num_test_cases):
        """
        Generate assembly test cases for a branch instruction.

        Args:
            instr_name (str): Branch instruction (e.g., 'beq', 'bne', etc.)
            condition_func (func): A Python function that takes (a, b) and returns True if branch should be taken
            num_test_cases (int): Number of test cases to generate
        """
        self.write_test_start()
        for test_code in range(num_test_cases):
            # give equal weight to equal and nonequal values
            if random.randint(0, 1) == 1:
                a = self.rand_nbit(32, True)
                b = self.rand_nbit(32, True)
            else:
                a = self.rand_nbit(32, True)
                b = a
            should_branch = condition_func(a, b)
            label1 = f"test_case_{test_code}_branch"
            label2 = f"test_case_{test_code}_branch_correct_skip"
            self.emit_li("t0", a)   # input 1
            self.emit_li("t1", b)   # input 2
            self.write_instr(f"{instr_name} t0, t1, {label1}\n")    # test instruction
            if should_branch:
                self.write_instr("j fail")
                self.label(label1)
            else:
                self.write_instr(f"j {label2}")
                self.label(label1)
                self.write_instr(f"j fail")
                self.label(label2)
        self.write_test_end()
        filename = f"{instr_name}.S"
        shutil.move(filename, self.asm_dir / filename)

    def write_utype_test(self, instr_name, num_test_cases, is_auipc):
        """
        Generate test cases for U-type instructions: LUI and AUIPC.

        Args:
            instr_name (str): 'lui' or 'auipc'
            num_test_cases (int): Number of test cases to generate
            is_auipc (bool): Whether the instruction is AUIPC (needs PC offset)
        """
        self.write_test_start()

        for test_code in range(num_test_cases):
            # 20-bit unsigned immediate
            imm = self.rand_nbit(20, False)
            if is_auipc:
                expected_value = self.trunc_32bits((imm << 12) + self.current_pc())
            else:
                expected_value = self.trunc_32bits(imm << 12)

            self.comment(f"Test Case: {test_code}")
            self.write_instr(f"{instr_name} t2, {imm}")
            self.emit_li("t3", expected_value)
            #self.emit_li("a1", test_code) # store current test case id
            self.test_write_check_eq("t2", "t3")

        self.write_test_end()
        filename = f"{instr_name}.S"
        shutil.move(filename, self.asm_dir / filename)

    def write_jtype_test(self, instr_name, num_test_cases, is_jalr):
        """
        Generate test cases for jump instructions: JAL and JALR.

        Args:
            instr_name (str): 'jal' or 'jalr'
            num_test_cases (int): Number of test cases to generate
            is_jalr (bool): Whether the instruction is JALR
        """
        self.write_test_start()
        for test_code in range(num_test_cases):
            # 12-bit signed immediate
            #offset = utils.reinterpret_signed(utils.rand_nbit(12, True) & ~3) # mask lower 2 bits so it is word aligned
            offset = self.rand_nbit(6, False) & ~3 # use only positive offsets for now in a small range
            rd = "ra" # register to store the actual return address 
            test_case_reg = "a1" # register to hold the current test case number
            expected_reg = "t2" # register to store the expected return address
            self.comment(f"Test Case: {test_code}")
            
            jump_label = f"skip_{test_code}"
            # jump to address and place return address in rd
            if is_jalr:
                rs1 = "t1" # register value added to immediate offset
                #rs1_value = self.reinterpret_signed(self.rand_nbit(32, True) & ~3)
                rs1_value = (self.rand_nbit(6, False) & ~3) + self.current_pc() # use only positive values for now in a small range, add current pc for easier testing
                self.emit_li(rs1, rs1_value)
                jump_offset = offset + rs1_value - self.current_pc() # assume always a forward jump
                expected_return_addr = self.current_pc() + 4
                self.comment(f"tracked pc = {self.to_hex32_str(self.current_pc())}")
                self.write_instr(f"{instr_name} {rd}, {rs1}, {offset}")
                
            else:
                jump_offset = offset
                expected_return_addr = self.current_pc() + 4
                self.comment(f"tracked pc = {self.to_hex32_str(self.current_pc())}")
                self.write_instr(f"{instr_name} {rd}, {jump_label}")

            if (jump_offset - 4) > 0:    # only pad if the offset results in a jump further than the instruction immediately after jalr 
                num_pad_instructions = (jump_offset - 4) >> 2
            else:
                num_pad_instructions = 0
            if 0:
                print(f"jump offset: {jump_offset}, num_pad_instrs: {num_pad_instructions}")
            for _ in range(num_pad_instructions):   # pad with jump instructions to fail loop up to the jump address
                self.write_instr(f"j fail") # catches if the cpu does not jump
            self.label(jump_label) # should jump to here
            # return address should be the next instruction
            # should fail if jump does not happen
            self.emit_li(expected_reg, expected_return_addr)
            self.emit_li(test_case_reg, test_code)
            self.test_write_check_eq(rd, expected_reg) # catches if the cpu stores the wrong jump address
        self.write_test_end()
        filename = f"{instr_name}.S"
        shutil.move(filename, self.asm_dir / filename) 

    def reinterpret_signed(self, value, bits):
        """
        Reinterpret a value as a signed N-bit integer.
        Example: reinterpret_signed(0xFFF, 12) → -1
        """
        mask = (1 << bits) - 1
        value &= mask
        sign_bit = 1 << (bits - 1)
        return value if value < sign_bit else value - (1 << bits)

    def reinterpret_unsigned(self, value, bits):
        """
        Reinterpret a value as an unsigned N-bit integer.
        Example: reinterpret_unsigned(-1, 32) → 0xFFFFFFFF
        """
        mask = (1 << bits) - 1
        return value & mask

    # instruction specific conversion functions for finding expected result
    def slt_signed(self, a, b):
        """
        calculates SLT instruction result for assembly test

        Args:
            a (int): signed 32-bit number on LHS
            b (int): signed 32-bit number on RHS
        Returns:
            int: returns 1 if a is less than b, else 0
        """
        if a < b:
            return 1
        else:
            return 0
        
    def slt_unsigned(self, a, b):
        """
        calculates SLTU instruction result for assembly test

        Args:
            a (int): signed 32-bit number on LHS
            b (int): signed 32-bit number on RHS
        Returns:
            int: returns 1 if a is less than b, else 0 when interpreting numbers as unsigned
        """
        if self.reinterpret_unsigned(a, 32) < self.reinterpret_unsigned(b, 32):
            return 1
        else:
            return 0
    def rand_nbit(self, num_bits, is_signed):
        """
        Returns a random n-bit number
        Args:
            num_bits (int): number of bits of the random number
            is_signed (bool): returns a signed number if true, else unsigned
        Returns:
            int: the random number
        """
        return random.randint(-2 ** (num_bits - 1), (2 ** (num_bits - 1) - 1) ) if is_signed else random.randint(0, (2 ** (num_bits - 1)))
    
    def trunc_32bits(self, a):
        """
        Truncate number 32-bits 
        Args:
            a (int): the number to truncate
        """
        return  a & 0xFFFF_FFFF
    


def create_all_tests(asm_dir):
    for name in ["add", "sub", "and", "or", "xor", "sll", "slt", "sltu", "srl", "sra",
                 "addi", "andi", "ori", "xori", "slli", "slti", "sltiu", "srli", "srai",
                 "beq", "bne", "blt", "bge", "bltu", "bgeu", "lui", "auipc", "jal", "jalr"
                
                ]:
        with open(f"{name}.S", "w") as f:
            gen = AsmWriter(f, asm_dir)  # new generator and new writer for each file
            match name:
                case "add":
                    gen.gen_r_itype_test(name, lambda a, b: a + b, 10)
                case "sub":
                    gen.gen_r_itype_test(name, lambda a, b: a - b, 10)
                case "and":
                    gen.gen_r_itype_test(name, lambda a, b: a & b, 10)
                case "or":
                    gen.gen_r_itype_test(name, lambda a, b: a | b, 10)
                case "xor":
                    gen.gen_r_itype_test(name, lambda a, b: a ^ b, 10)
                case "sll":
                    gen.gen_r_itype_test(name, lambda a, b: (a << (b & 0x1F)), 10, False, True)
                case "slt":
                    gen.gen_r_itype_test(name, gen.slt_signed, 10)
                case "sltu":
                    gen.gen_r_itype_test(name, gen.slt_unsigned, 10)
                case "srl":
                    gen.gen_r_itype_test(name, lambda a, b: (gen.reinterpret_unsigned(a, 32) >> (b & 0x1F)), 10, False, True)
                case "sra":
                    gen.gen_r_itype_test(name, lambda a, b: (a >> (b & 0x1F)), 10)
                case "addi":
                    gen.gen_r_itype_test(name, lambda a, b: a + b, 10, True)
                case "andi":
                    gen.gen_r_itype_test(name, lambda a, b: a & b, 10, True)
                case "ori":
                    gen.gen_r_itype_test(name, lambda a, b: a | b, 10, True)
                case "xori":
                    gen.gen_r_itype_test(name, lambda a, b: a ^ b, 10, True)
                case "slli":
                    gen.gen_r_itype_test(name, lambda a, b: (a << (b & 0x1F)), 10, True, True)
                case "slti":
                    gen.gen_r_itype_test(name, gen.slt_signed, 10, True)
                case "sltiu":
                    gen.gen_r_itype_test(name, gen.slt_unsigned, 10, True)
                case "srli":
                    gen.gen_r_itype_test(name, lambda a, b: (gen.reinterpret_unsigned(a, 32) >> (b & 0x1F)), 10, True, True)
                case "srai":
                    gen.gen_r_itype_test(name, lambda a, b: (a >> (b & 0x1F)), 10, True, True)
                case "beq":
                    gen.gen_btype_test(name, lambda a, b: (a == b), 100)
                case "bne":
                    gen.gen_btype_test(name, lambda a, b: (a != b), 100)
                case "blt":
                    gen.gen_btype_test(name, lambda a, b: (a < b), 100)
                case "bge":
                    gen.gen_btype_test(name, lambda a, b: (a >= b), 100)
                case "bltu":
                    gen.gen_btype_test(name, lambda a, b: (gen.reinterpret_unsigned(a, 32) < gen.reinterpret_unsigned(b, 32)), 100)
                case "bgeu":
                    gen.gen_btype_test(name, lambda a, b: (gen.reinterpret_unsigned(a, 32) >= gen.reinterpret_unsigned(b, 32)), 100) 
                case "lui":
                    gen.write_utype_test(name, 10, False)
                case "auipc":
                    gen.write_utype_test(name, 10, True)   
                case "jal":
                    gen.write_jtype_test(name, 4, False)
                case "jalr":
                    gen.write_jtype_test(name, 4, True)   
                case _:
                    raise Exception("unknown assembly test!")
                
def process_tests(asm_dir, hex_dir, dump_dir):
    """
    Process assembly files to be converted to hex files
        asm_dir (Path): directory of assembly files
        hex_dir (Path): directory of hex files
        dump_dir (Path): directory of dump files
    """
    
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