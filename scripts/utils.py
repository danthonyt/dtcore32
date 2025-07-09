# utils.py
import random

# Assembly file writing functions
# valid registers for riscv32i ISA
VALID_REGS = {
    f'x{i}' for i in range(32)
} | {
    'zero', 'ra', 'sp', 'gp', 'tp',
    't0', 't1', 't2', 't3', 't4', 't5', 't6',
    's0', 's1', 's2', 's3', 's4', 's5', 's6', 's7', 's8', 's9', 's10', 's11',
    'a0', 'a1', 'a2', 'a3', 'a4', 'a5', 'a6', 'a7'
}

def write_start(f):
    f.write(".section .text\n.global _start\n_start:\n")
    # reset all registers to 0 at the start of the test
    f.write(f"  li t0, 0\n")
    f.write(f"  li t1, 0\n")
    f.write(f"  li t2, 0\n")
    f.write(f"  li t3, 0\n")
    f.write(f"  li t4, 0\n")
    f.write(f"  li t5, 0\n")
    f.write(f"  li a0, 0\n")
    f.write(f"  li a1, 0\n")
    f.write(f"  li a2, 0\n")
    f.write(f"  li a3, 0\n")
    f.write(f"  li a4, 0\n")
    f.write(f"  li a5, 0\n")
    f.write(f"  li a6, 0\n")
    f.write(f"  li a7, 0\n")
    f.write(f"  li s0, 0\n")
    f.write(f"  li s1, 0\n")
    f.write(f"  li s2, 0\n")
    f.write(f"  li s3, 0\n")
    f.write(f"  li s4, 0\n")
    f.write(f"  li s5, 0\n")
    f.write(f"  li s6, 0\n")
    f.write(f"  li s7, 0\n")
    f.write(f"  li s8, 0\n")
    f.write(f"  li s9, 0\n")
    f.write(f"  li s10, 0\n")
    f.write(f"  li s11, 0\n\n")

def write_end(f):
    # pass and fail codes and loop forever
    f.write("pass:\n")
    f.write(f"  li a0, 0\n")
    f.write(f"  li a7, 93\n")
    f.write(f"  li gp, 1\n")
    f.write(f"  ecall\n")
    f.write(f"  j pass\n")
    f.write(f"fail:\n")
    f.write(f"  li a0, 0\n")
    f.write(f"  li a7, 93\n")
    f.write(f"  li gp, 0\n")
    f.write(f"  ecall\n")
    f.write(f"  j fail\n")

def write_check_eq(f,reg1, reg2):
    for reg in (reg1, reg2):
        if reg not in VALID_REGS:
            raise ValueError(f"Invalid register: '{reg}'")
    f.write(f"  bne {reg1}, {reg2}, fail\n") 
# math functions

def rand_32bit_signed():
    return random.randint(-2**31, 2**31 - 1)

def to_hex32_str(val):
    return f"0x{val & 0xFFFFFFFF:08x}"

def trunc_32bits(a):
    return  a & 0xFFFFFFFF
def to_32signed(a):
    """
    Reinterpret a number as 32 bit signed
    """
    return a if a < 0x8000_0000 else a - 0x1_0000_0000
def to_32unsigned(a):
    """
    Reinterpret a number as 32-bit unsigned
    """
    return a & 0xFFFF_FFFF