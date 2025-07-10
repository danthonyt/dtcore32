# test_generator.py
import utils
import random
from pathlib import Path
import shutil

'''

def write_utype_test(instr_name, num_test_cases, is_auipc):
    """
    Generate test cases for U-type instructions: LUI and AUIPC.

    Args:
        instr_name (str): 'lui' or 'auipc'
        num_test_cases (int): Number of test cases to generate
        is_auipc (bool): Whether the instruction is AUIPC (needs PC offset)
    """
    pc = 0
    filename = f"{instr_name}.S"

    with open(filename, "w") as f:
        pc += utils.write_start(f)

        for test_code in range(num_test_cases):
            # 20-bit unsigned immediate
            imm = utils.rand_nbit(20, False)

            if is_auipc:
                result = utils.trunc_32bits((imm << 12) + pc)
            else:
                result = utils.trunc_32bits(imm << 12)

            f.write(f"# Test Case {test_code}, PC = 0x{pc:08x}\n")
            f.write(f"  {instr_name} t2, {imm}\n")
            f.write(f"  li t3, {utils.to_hex32_str(result)}  # expected\n") # this will be 2 instructions
            f.write(f"  li x11, {utils.to_hex32_str(test_code)}  # test case id\n")
            f.write(f"  bne t2, t3, fail\n\n")

            pc += 4 * 5  

        utils.write_end(f)

    shutil.move(filename, asm_dir / filename)

def write_jumptype_test(instr_name, num_test_cases, is_jalr):
    """
    Generate test cases for jump instructions: JAL and JALR.

    Args:
        instr_name (str): 'jal' or 'jalr'
        num_test_cases (int): Number of test cases to generate
        is_jalr (bool): Whether the instruction is JALR
    """
    pc = 0
    filename = f"{instr_name}.S"

    with open(filename, "w") as f:
        pc += utils.write_start(f)

        for test_code in range(num_test_cases):
            # 12-bit signed immediate
            #offset = utils.reinterpret_signed(utils.rand_nbit(12, True) & ~3) # mask lower 2 bits so it is word aligned
            offset = utils.reinterpret_signed(utils.rand_nbit(6, False) & ~3) # use only positive offsets for now in a small range
            rd = "ra" # register to store the actual return address 
            test_case_reg = "a1" # register to hold the current test case number
            expected_reg = "t2" # register to store the expected return address

            f.write(f"# Test Case {test_code}, PC = 0x{pc:08x}\n")
            
            expected_jump_addr = pc + 4
            # jump to address and place return address in rd
            if is_jalr:
                rs1 = "t1" # register value added to immediate offset
                #rs1_value = utils.reinterpret_signed(utils.rand_nbit(32, True) & ~3)
                rs1_value = utils.reinterpret_signed((utils.rand_nbit(6, False) & ~3 + pc)) # use only positive values for now in a small range, add current pc for easier testing
                f.write(f"  lui {rs1}, {utils.to_hex32_str((rs1_value & 0xFFFF_F000) >> 12)}  \n")
                f.write(f"  addi {rs1}, {utils.to_hex32_str((rs1_value & 0x0000_0FFF))}  \n")
                f.write(f"  {instr_name} {rd}, {rs1}, {offset}\n")
                pc += 4 * 2
                jump_offset = offset + rs1_value
                if jump_offset > 0:
                    num_pad_instructions = jump_offset >> 2
                else:
                    num_pad_instructions = 0
            else:
                jump_offset = offset + pc
                f.write(f"  {instr_name} {rd}, {offset}\n")
                pc += 4 * 1
                if offset > 0:
                    num_pad_instructions = offset >> 2
                else:
                    num_pad_instructions = 0
                num_pad_instructions = offset >> 2
            for _ in range(num_pad_instructions):   # pad with jump instructions to fail loop up to the jump address
                f.write(f"  j fail\n") # catches if the cpu does not jump
                pc += 4 * 1
            # return address should be the next instruction
            # should fail if jump does not happen
            f.write(f"  lui {expected_reg}, {utils.to_hex32_str((expected_jump_addr & 0xFFFF_F000) >> 12)}  \n")
            f.write(f"  addi {expected_reg}, {utils.to_hex32_str((expected_jump_addr & 0x0000_0FFF))}  \n")
            f.write(f"  lui {test_case_reg}, {utils.to_hex32_str((test_code & 0xFFFF_F000) >> 12)}  \n")
            f.write(f"  addi {test_case_reg}, {utils.to_hex32_str((test_code & 0x0000_0FFF))}  \n")
            f.write(f"  bne {rd}, {expected_reg}, fail\n\n") # cathches if the cpu stores the wrong jump address
            pc += 4 * 5

              

        utils.write_end(f)

    shutil.move(filename, asm_dir / filename)    


def write_branch_test(instr_name, condition_func, num_test_cases):
    """
    Generate assembly test cases for a branch instruction.

    Args:
        instr_name (str): Branch instruction (e.g., 'beq', 'bne', etc.)
        condition_func (func): A Python function that takes (a, b) and returns True if branch should be taken
        num_test_cases (int): Number of test cases to generate
    """
    filename = f"{instr_name}.S"
    with open(filename, "w") as f:
        utils.write_start(f)
        for test_code in range(num_test_cases):
            # give equal weight to equal and nonequal values
            if random.randint(0, 1) == 1:
                a = utils.rand_nbit(32, True)
                b = utils.rand_nbit(32, True)
            else:
                a = utils.rand_nbit(32, True)
                b = a
            should_branch = condition_func(a, b)

            label1 = f"test_case_{test_code}_branch"
            label2 = f"test_case_{test_code}_branch_correct_skip"
            f.write(f"  li x1, {utils.to_hex32_str(a)}\n")
            f.write(f"  li x2, {utils.to_hex32_str(b)}\n")
            f.write(f"  {instr_name} x1, x2, {label1}\n")
            if should_branch:
                f.write(f"  j fail\n")
                f.write(f"{label1}:\n")
            else:
                f.write(f"  j {label2}\n")
                f.write(f"{label1}:\n")
                f.write(f"  j fail\n")
                f.write(f"{label2}:\n")
        utils.write_end(f)
    shutil.move(filename, asm_dir / filename)



write_branch_test("beq",lambda a, b: (a == b), 100)
write_branch_test("bne",lambda a, b: (a != b), 100)
write_branch_test("blt",lambda a, b: (a < b), 100)
write_branch_test("bge",lambda a, b: (a >= b), 100)
write_branch_test("bltu",lambda a, b: (utils.reinterpret_unsigned(a, 32) < utils.reinterpret_unsigned(b, 32)), 100)
write_branch_test("bgeu",lambda a, b: (utils.reinterpret_unsigned(a, 32) >= utils.reinterpret_unsigned(b, 32)), 100)

write_utype_test("lui", 100, False)
write_utype_test("auipc", 100, True)

write_jumptype_test("jal", 100, False)
write_jumptype_test("jalr", 100, True)
'''

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

