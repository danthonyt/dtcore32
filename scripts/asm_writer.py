import random
import os
import subprocess
import random
from pathlib import Path
import shutil
import numpy as np

class AsmWriter:
    def __init__(self, file_handle, asm_dir, start_address=0x0, dmem_start_address=0x2000, dmem_size=0x400):
        self.f = file_handle
        self.asm_dir = asm_dir
        self.pc = start_address
        self.dmem_start_address = dmem_start_address
        self.dmem_size = dmem_size
        self.labels = {}
        self.test_case_id = 0
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
        self.test_case_reg = self.named_regs["a1"]
        self.reserved_regs = {
            self.test_case_reg
        }

    def random_regs_unique(self):
        # Candidates for rd: exclude x0 + reserved
        rd_candidates = [i for i in range(1, 32) if i not in self.reserved_regs]
        rs_candidates = [i for i in range(0, 32) if i not in self.reserved_regs]

        rd_num = random.choice(rd_candidates)
        rs_candidates.remove(rd_num)

        rs1_num = random.choice(rs_candidates)
        rs_candidates.remove(rs1_num)

        rs2_num = random.choice(rs_candidates)

        return f'x{rd_num}', f'x{rs1_num}', f'x{rs2_num}'

    def write_generate_random_dmem(self):
        """
        Initialize data memory of a specified size to random values in assembly file
        """
        self.write_directive(".data")

        array_str = ""

        for i in range(self.dmem_size):
            rand_8bit = rand_nbit(8, False)
            if i == self.dmem_size-1:
                array_str += f"0x{rand_8bit & 0xFF:02x}"
            else:
                array_str += f"0x{rand_8bit & 0xFF:02x},"
        self.write_directive(f"array: .byte {array_str}")

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
        """
        returns the current instruction address of the generated assembly file
        Returns:
            int: the current pc
        """
        return self.pc

    def get_label_address(self, name):
        """
        returns the address associated with a label
        Args:
            int: the label address
        """
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
        # or load all registers with a random value
        for name in self.dest_registers:
            #self.write_instr(f"addi {name}, x0, 0")
            self.emit_li(name, rand_nbit(32, False))

    def write_test_end(self):
        """
        Generate the pass and fail loops at the end of an assembly test
        """
        self.write_instr("ecall")

    def track_test_case(self):
        """
        stores the current test case id into a register for error checking
        """
        self.emit_li(self.test_case_reg, self.test_case_id) # test case id
        self.test_case_id += 1

    def comment_test_case(self):
        """
        comments in the assembly code the current test case
        """
        self.comment(f"test case {self.test_case_id}")

    def move_asm_file(self, filename):
        """
        moves a file to the designated assembly file directory
        Args:
            filename (str): the name of the file to move
        """
        shutil.move(filename, self.asm_dir / filename)

    def test_write_check_eq(self, reg1, reg2):
        """
        compares a resulting register value to the expected register value
        Args:
            reg1 (str): the register holding the actual value
            reg2 (str): the register holding the expected value
        """
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
    
    def gen_r_itype_test(self, instr_name, num_test_cases, is_immediate=False, is_shift=False):
        """
        Generate the assembly file for an R-type or I-type instruction (add, sub, or, etc.)

        Args:
            instr_name (str): The RISC-V instruction name (e.g., 'add', 'sub', 'or')
            num_test_cases (int): Number of test cases to generate
            is_immediate (bool): indicates whether or not the instruction uses immediates
            is_shift (bool): indicates whether or not the instruction is a shift instruction
        """
        self.write_test_start()
        for _ in range(num_test_cases):
            a = rand_nbit(32, True)
            self.comment_test_case()
            self.track_test_case()
            rd, rs1, rs2 = self.random_regs_unique()
            if is_immediate:
                # generate random 12-bit signed immediate
                imm = rand_nbit(12, True)
                if is_shift:
                    imm = imm & 0x1F
                self.write_instr(f"{instr_name} {rd}, {rs1}, {imm}")
            else:
                b = rand_nbit(32, True)
                self.emit_li(rs2, b) 
                self.write_instr(f"{instr_name} {rd}, {rs1}, {rs2}")
        self.write_test_end()
        self.move_asm_file(f"{instr_name}.S")

    def gen_btype_test(self, instr_name, condition_func, num_test_cases):
        """
        Generate assembly test cases for a branch instruction.

        Args:
            instr_name (str): Branch instruction (e.g., 'beq', 'bne', etc.)
            condition_func (func): A Python function that takes (a, b) and returns True if branch should be taken
            num_test_cases (int): Number of test cases to generate
        """
        self.write_test_start()
        
        for _ in range(num_test_cases):
            rd, rs1, rs2 = self.random_regs_unique()
            self.track_test_case()
            # give equal weight to equal and nonequal values
            if random.randint(0, 1) == 1:
                a = rand_nbit(32, True)
                b = rand_nbit(32, True)
            else:
                a = rand_nbit(32, True)
                b = a
            should_branch = condition_func(a, b)
            label1 = f"test_case_{self.test_case_id}_branch"
            label2 = f"test_case_{self.test_case_id}_branch_correct_skip"
            self.emit_li(rs1, a)   
            self.emit_li(rs2, b)
            self.write_instr(f"{instr_name} {rs1}, {rs2}, {label1}")    # test instruction
            if should_branch:
                self.emit_li(rd, 0xFBAD)    # store this value for correct branch
                self.label(label1)
            else:
                self.write_instr(f"j {label2}")
                self.label(label1)
                self.emit_li(rd, 0xFBAD)
                self.label(label2)
                self.emit_li(rd, 0xDAAD)    # store this value for wrong branch
        self.write_test_end()
        self.move_asm_file(f"{instr_name}.S")

    def write_utype_test(self, instr_name, num_test_cases):
        """
        Generate test cases for U-type instructions: LUI and AUIPC.

        Args:
            instr_name (str): 'lui' or 'auipc'
            num_test_cases (int): Number of test cases to generate
        """
        self.write_test_start()
        for _ in range(num_test_cases):
            rd, _, _ = self.random_regs_unique()
            self.comment_test_case()
            self.track_test_case()
            # 20-bit unsigned immediate
            imm = rand_nbit(20, False)
            if instr_name != "auipc" and instr_name != "lui":
                raise Exception(f"unknown utype instruction: {instr_name}")
            self.write_instr(f"{instr_name} {rd}, {imm}")
        self.write_test_end()
        self.move_asm_file(f"{instr_name}.S")

    def write_jtype_test(self, instr_name, num_test_cases):
        """
        Generate test cases for jump instructions: JAL and JALR.

        Args:
            instr_name (str): 'jal' or 'jalr'
            num_test_cases (int): Number of test cases to generate
        """
        self.write_test_start()
        for _ in range(num_test_cases):
            # 12-bit signed immediate
            #offset = utils.reinterpret_signed(utils.rand_nbit(12, True) & ~3) # mask lower 2 bits so it is word aligned
            offset = rand_nbit(6, False) & ~3 # use only positive offsets for now in a small range
            rd, rs1, _ = self.random_regs_unique()
            self.comment_test_case()
            jump_label = f"skip_{self.test_case_id}"
            # jump to address and place return address in rd
            if instr_name == "jalr":
                #rs1_value = reinterpret_signed(rand_nbit(32, True) & ~3)
                rs1_value = (rand_nbit(6, False) & ~3) + self.current_pc() + 8  # use only positive values for now in a small range, add pc of load instruction for easier testing
                self.emit_li(rs1, rs1_value)
                jump_offset = offset + rs1_value - self.current_pc() # assume always a forward jump
                self.write_instr(f"{instr_name} {rd}, {rs1}, {offset}")
            elif instr_name == "jal":
                jump_offset = offset
                self.write_instr(f"{instr_name} {rd}, {jump_label}")
            else:
                raise Exception(f"unknown jtype instruction: {instr_name}")

            if (jump_offset - 4) > 0:    # only pad if the offset results in a jump further than the instruction immediately after jalr 
                num_pad_instructions = (jump_offset - 4) >> 2
            else:
                num_pad_instructions = 0
            #print(f"jump offset: {jump_offset}, num_pad_instrs: {num_pad_instructions}")
            for _ in range(num_pad_instructions):   # pad with jump instructions to fail loop up to the jump address
                random_result_reg, _, _ = self.random_regs_unique() 
                self.emit_li(random_result_reg, 0xFBAD) # load for an incorrect jump
            self.label(jump_label) # should jump to here
            # return address should be the next instruction
            # should fail if jump does not happen
            self.track_test_case()
        self.write_test_end()
        self.move_asm_file(f"{instr_name}.S")

    def gen_ltype_test(self, instr_name, num_test_cases):
        """
        Generate the assembly file for a load instruction (lb, lh, lw, etc.)

        Args:
            instr_name (str): The RISC-V instruction name 
            num_test_cases (int): Number of test cases to generate
        """
        self.write_generate_random_dmem()
        self.write_test_start()
        
        rd, rs1, _ = self.random_regs_unique()
        for _ in range(num_test_cases):
            self.comment_test_case()
            # offset + value(rs1) should not exceed the memory depth-1 of the data memory
            # in this instance we have a depth of 1024, so random_addr = imm_offset + value(rs1) < 1024 10 bit limit
            match instr_name:
                case "lb":
                    imm_offset = rand_nbit(8, False)
                    base_addr = rand_nbit(9, False) + self.dmem_start_address
                case "lh":
                    imm_offset = (rand_nbit(8, False) & ~0x1)
                    base_addr = (rand_nbit(9, False) & ~0x1) + self.dmem_start_address
                    # addr must be half-word aligned
                case "lw":
                    imm_offset = (rand_nbit(8, False) & ~0x3)
                    base_addr = (rand_nbit(9, False) & ~0x3) + self.dmem_start_address
                    # addr must be word aligned
                case "lbu":
                    imm_offset = rand_nbit(8, False)
                    base_addr = rand_nbit(9, False) + self.dmem_start_address
                case "lhu":
                    imm_offset = (rand_nbit(8, False) & ~0x1)
                    base_addr = (rand_nbit(9, False) & ~0x1) + self.dmem_start_address
                case _:
                    raise Exception("Unknown load instruction!")   
            self.emit_li(rs1, base_addr)
            self.write_instr(f"{instr_name} {rd}, {imm_offset}({rs1})")
            self.track_test_case()
        self.write_test_end()
        self.move_asm_file(f"{instr_name}.S")

    def gen_stype_test(self, instr_name, num_test_cases):
        """
        Generate the assembly file for a store instruction (sb, sh, etc.)

        Args:
            instr_name (str): The RISC-V instruction name 
            num_test_cases (int): Number of test cases to generate
        """
        self.write_test_start()
        _, rs1, rs2 = self.random_regs_unique()
        random_wr_data = rand_nbit(32, False)
        for _ in range(num_test_cases):
            self.comment_test_case()
            
            match instr_name:
                case "sb":
                    imm_offset = rand_nbit(8, False)
                    base_addr = rand_nbit(9, False) + self.dmem_start_address
                case "sh":
                    imm_offset = rand_nbit(8, False) & ~0x1
                    base_addr = (rand_nbit(9, False) + self.dmem_start_address) & ~0x1
                case "sw":
                    imm_offset = rand_nbit(8, False) & ~0x3
                    base_addr = (rand_nbit(9, False) + self.dmem_start_address) & ~0x3
                case _:
                    raise Exception("Unknown load instruction!")   
            self.emit_li(rs2, random_wr_data)  
            self.emit_li(rs1, base_addr)
            self.write_instr(f"{instr_name} {rs2}, {imm_offset}({rs1})") # store instruction
            self.track_test_case()
        self.write_test_end()
        self.move_asm_file(f"{instr_name}.S")
    '''
    def gen_data_hazard_test(self, data_hazard_type, num_test_cases):
        """
        Generate the assembly file for testing data hazards

        Args:
            data_hazard_type (str): The data hazard being tested
            num_test_cases (int): Number of test cases to generate
        """
        self.write_test_start()
        for _ in range(num_test_cases):
            self.comment_test_case()
            test_case_reg = "a1"
            match data_hazard_type:
                case "data_hazard_alu_to_alu":
                    instr1_rd = "t0"
                    instr1_rs1 = "t1"
                    instr1_rs2 = "t2"
                    instr2_rd = "t3"
                    expected_result_reg = "t4"

                    self.emit_li(instr1_rs1, instr1_rs1_value)
                    self.emit_li(instr1_rs2, instr1_rs2_value)


                    instr1_rs1_value = rand_nbit(32, False)
                    instr1_rs2_value = rand_nbit(32, False)
                    instr1_rd_value = instr1_rs1_value + instr1_rs2_value
                    # randomly choose rs1 or rs2 for the dependent register
                    if random.randint(0,1) == 1:
                        instr2_rs1 = instr1_rd
                        instr2_rs2 = "t5"
                        instr2_rs1_value = instr1_rd_value
                        instr2_rs2_value = rand_nbit(32, False)
                        self.emit_li(instr2_rs2, instr2_rs2_value)
                    else:
                        instr2_rs1 = "t5"
                        instr2_rs2 = instr1_rd
                        instr2_rs1_value = rand_nbit(32, False)
                        instr2_rs2_value = instr1_rd_value
                        self.emit_li(instr2_rs1, instr2_rs1_value)
                    expected_instr2_rd_value = instr2_rs1_value - instr2_rs2_value
                    
                    self.emit_li(expected_result_reg, expected_instr2_rd_value)
                    # use add and sub instruction for 1st and 2nd instruction respectively, for now
                    self.write_instr(f"add {instr1_rd}, {instr1_rs1}, {instr1_rs2}")
                    self.write_instr(f"sub {instr2_rd}, {instr2_rs1}, {instr2_rs2}")
                    self.test_write_check_eq(expected_result_reg, instr2_rd)
                case "data_hazard_load_to_alu":
                    load_instr_rd = "t0"
                    load_instr_rs1 = "t1"
                    load_instr_offset = rand_nbit(6, False)
                case "data_hazard_alu_to_store":
                case "data_hazard_load_to_store":
                case _:
                    raise Exception("Unknown load instruction!")   
            self.track_test_case(test_case_reg)
        self.write_test_end()
        self.move_asm_file(f"{data_hazard_type}.S")
    
    '''
    
def reinterpret_signed(value, bits):
    """
    Reinterpret a value as a signed N-bit integer.
    Example: reinterpret_signed(0xFFF, 12) → -1
    """
    mask = (1 << bits) - 1
    value &= mask
    sign_bit = 1 << (bits - 1)
    return value if value < sign_bit else value - (1 << bits)

def reinterpret_unsigned(value, bits):
    """
    Reinterpret a value as an unsigned N-bit integer.
    Example: reinterpret_unsigned(-1, 32) → 0xFFFFFFFF
    """
    mask = (1 << bits) - 1
    return value & mask

def rand_nbit(num_bits, is_signed):
    """
    Returns a random n-bit number
    Args:
        num_bits (int): number of bits of the random number
        is_signed (bool): returns a signed number if true, else unsigned
    Returns:
        int: the random number
    """
    return random.randint(-2 ** (num_bits - 1), (2 ** (num_bits - 1) - 1) ) if is_signed else random.randint(0, (2 ** (num_bits - 1)))
    
def trunc_32bits(a):
    """
    Truncate number 32-bits 
    Args:
        a (int): the number to truncate
    """
    return  a & 0xFFFF_FFFF

def create_all_tests(asm_dir):
    for name in ["add", "sub", "and", "or", "xor", "sll", "slt", "sltu", "srl", "sra",
                 "addi", "andi", "ori", "xori", "slli", "slti", "sltiu", "srli", "srai",
                 "beq", "bne", "blt", "bge", "bltu", "bgeu", "lui", "auipc", "jal", "jalr",
                 "lb", "lh", "lw", "lbu", "lhu", "sb", "sh", "sw"
                ]:
        with open(f"{name}.S", "w") as f:
            gen = AsmWriter(f, asm_dir)  # new generator and new writer for each file
            match name:
                case "add":
                    gen.gen_r_itype_test(name, 10)
                case "sub":
                    gen.gen_r_itype_test(name, 10)
                case "and":
                    gen.gen_r_itype_test(name, 10)
                case "or":
                    gen.gen_r_itype_test(name, 10)
                case "xor":
                    gen.gen_r_itype_test(name, 10)
                case "sll":
                    gen.gen_r_itype_test(name, 10, False, True)
                case "slt":
                    gen.gen_r_itype_test(name, 10)
                case "sltu":
                    gen.gen_r_itype_test(name, 10)
                case "srl":
                    gen.gen_r_itype_test(name, 10, False, True)
                case "sra":
                    gen.gen_r_itype_test(name, 10)
                case "addi":
                    gen.gen_r_itype_test(name, 10, True)
                case "andi":
                    gen.gen_r_itype_test(name, 10, True)
                case "ori":
                    gen.gen_r_itype_test(name, 10, True)
                case "xori":
                    gen.gen_r_itype_test(name, 10, True)
                case "slli":
                    gen.gen_r_itype_test(name, 10, True, True)
                case "slti":
                    gen.gen_r_itype_test(name, 10, True)
                case "sltiu":
                    gen.gen_r_itype_test(name, 10, True)
                case "srli":
                    gen.gen_r_itype_test(name, 10, True, True)
                case "srai":
                    gen.gen_r_itype_test(name, 10, True, True)
                case "beq":
                    gen.gen_btype_test(name, lambda a, b: (a == b), 10)
                case "bne":
                    gen.gen_btype_test(name, lambda a, b: (a != b), 10)
                case "blt":
                    gen.gen_btype_test(name, lambda a, b: (a < b), 10)
                case "bge":
                    gen.gen_btype_test(name, lambda a, b: (a >= b), 10)
                case "bltu":
                    gen.gen_btype_test(name, lambda a, b: (reinterpret_unsigned(a, 32) < reinterpret_unsigned(b, 32)), 10)
                case "bgeu":
                    gen.gen_btype_test(name, lambda a, b: (reinterpret_unsigned(a, 32) >= reinterpret_unsigned(b, 32)), 10) 
                case "lui":
                    gen.write_utype_test(name, 10)
                case "auipc":
                    gen.write_utype_test(name, 10)   
                case "jal":
                    gen.write_jtype_test(name, 4)
                case "jalr":
                    gen.write_jtype_test(name, 4)
                case "lb":
                    gen.gen_ltype_test(name, 10)
                case "lh":
                    gen.gen_ltype_test(name, 10)
                case "lw":
                    gen.gen_ltype_test(name, 10)
                case "lbu":
                    gen.gen_ltype_test(name, 10)
                case "lhu":
                    gen.gen_ltype_test(name, 10)
                case "sb":
                    gen.gen_stype_test(name, 10)
                case "sh":
                    gen.gen_stype_test(name, 10)
                case "sw":
                    gen.gen_stype_test(name, 10)     
                case _:
                    raise Exception(f"unknown assembly test! {name}")
                
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
            def bin_to_swapped_hex_word(input_file, output_file):
                with open(input_file, "rb") as f_in, open(output_file, "w") as f_out:
                    while chunk := f_in.read(4):
                        if len(chunk) < 4:
                            chunk = chunk.ljust(4, b'\x00')
                        swapped = chunk[::-1].hex().upper()
                        f_out.write(swapped + "\n")

            def bin_to_swapped_hex_byte(input_file, output_file):
                with open(input_file, "rb") as f_in, open(output_file, "w") as f_out:
                    while chunk := f_in.read(1):
                        if len(chunk) < 1:
                            chunk = chunk.ljust(1, b'\x00')
                        swapped = chunk[::-1].hex().upper()
                        f_out.write(swapped + "\n")

            bin_to_swapped_hex_word(imem_bin, imem_hex)
            bin_to_swapped_hex_byte(dmem_bin, dmem_hex)

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