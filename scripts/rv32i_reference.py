# rv32i_reference.py
import os
from pathlib import Path
def sign_extend(val, bits):
    if val & (1 << (bits - 1)):
        val -= 1 << bits
    return val

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
    
class rv32i_cpu:
    def __init__(self, mem_size=4096):
        self.regs = [0] * 32
        self.pc = 0
        self.memory = bytearray(mem_size) 
        self.instructions = []  # parsed instructions
        self.is_halted = False

    def reset(self):
        self.regs = [0] * 32
        self.pc = 0
        self.memory.clear()
        self.instructions.clear()
        self.is_halted = False

    def load_program(self, test_name, test_dir):
        instructions = []
        file_path = Path(test_dir) / f"{test_name}.mem"

        with open(file_path, "r") as f:
            for line in f:
                line = line.strip()
                if line:  # Skip empty lines
                    try:
                        instructions.append(int(line, 16))  # Convert hex string to int
                    except ValueError:
                        raise ValueError(f"Invalid line in hex file: '{line}'")

        self.instructions = instructions
        self.pc = 0  # Optionally reset program counter
        # print(f"Loaded {len(instructions)} instructions from {file_path}")

    def run(self, is_print_statements_enabled):
        while (self.pc < len(self.instructions) * 4) and not (self.is_halted):
            if (self.pc & 0x3) != 0:
                raise Exception(f"Misaligned PC! {self.pc}")
            else:
                instr = self.instructions[self.pc // 4]
            self.fetch()
            decoded_instr = self.decode(instr)
            if is_print_statements_enabled:
                print(f'decoded instruction:{decoded_instr.get('op')}!')
                print(f'current pc: {hex(self.pc)} instruction number: {self.pc // 4}')
            self.execute(decoded_instr)

    def dump_registers(self):
        """
        Dumps the register state, used after running a test for comparison to a rv32i cpu implementation
        Returns:
            a 32 element array holding all register states
        """
        for index in range(0,32):
            print(f'register x{index}: {hex(self.regs[index])}')
        return self.regs.copy()
    
    def dump_memory(self):
        """
        Dumps the memory state, used after running a test for comparison to a rv32i cpu implementation
        Returns:
            an array holding all memory values
        """
        return dict(self.memory)
    
    def compare_cpu_regdumps(self, base_filename, dir, testname):
        """
        Compares the register and data memory dumps from the reference rv32i cpu and the 
        actual implementation of a rv32i cpu 
        Args:
            rv32i_regdump_filename(str): The file holding the implementation cpu's register dumps
            rv32i_dmemdump_filename(str): The file holding the implementation cpu's data memory dumps
        """
        file_str = dir + testname + base_filename
        with open(file_str, "r") as f:
            regnum = 0
            for line in f:
                line = line.strip()
                if line:  # Skip empty lines
                    ref_reg_value = self.regs[regnum]
                    impl_reg_value = int(line, 16)
                    if ref_reg_value != impl_reg_value:
                        raise Exception(f"test {testname} register x{regnum} does not match with the reference! reference: 0x{ref_reg_value:08x}, implementation: 0x{impl_reg_value:08x}")
                regnum = regnum + 1
            print(f"all registers match! test: {testname}")
    
    def incr_pc(self, incr_val=4):
        self.pc += incr_val

    def set_pc(self, pc_val):
        self.pc = pc_val


    def check_valid_reg(self,reg):
        """
        Does a check to ensure the accessed register is valid
        Returns:
            bool: True if the register is valid, else False
        """
        if type(reg) == 'int':
            raise Exception(f"Invalid data type for register! {type(reg)}")
        elif not ((reg >= 0) and (reg < 32)):
            raise Exception(f"Invalid index of register! {reg}")
        else:
            return True

    def write_reg(self, reg, value):
        """
        Writes a new value to a register
        Args:
            reg(int): The register index to write to (e.g. 1, 2, 3, ... ,31)
            value(int): The new value to write
        """
        if (reg != 0) and self.check_valid_reg(reg):
            self.regs[reg] = value & 0xFFFF_FFFF
            #print("tried to write to the zero register")
            #raise Exception("Error! Tried to write to the zero register!")
        
    def read_reg(self, reg):
        """
        Reads the current value held by a register
        Args:
            reg(int): The register index to write to (e.g. 1, 2, 3, ... ,31)
        Returns:
            int: The register value
        """
        if self.check_valid_reg(reg):
            return self.regs[reg]
        else:
            raise Exception("Register read error!") 
        
    def write_byte(self, addr, value):
        self.memory[addr] = value

    def write_halfword(self, addr, value):
        if (addr & 0x1) != 0:
            raise Exception("misaligned halfword write!")
        self.memory[addr] = value & 0xFF
        self.memory[addr + 1] = (value >> 8) & 0xFF

    def write_word(self, addr, value):
        if (addr & 0x3) != 0:
            raise Exception("misaligned word write!")
        self.memory[addr] = value & 0xFF
        self.memory[addr + 1] = (value >> 8) & 0xFF
        self.memory[addr + 2] = (value >> 16) & 0xFF
        self.memory[addr + 3] = (value >> 24) & 0xFF

    def read_byte(self, addr):
        return self.memory[addr]
    
    def read_halfword(self, addr):
        if (addr & 0x1) != 0:
            raise Exception("misaligned halfword read!")
        byte0 = self.read_byte(addr)
        byte1 = self.read_byte(addr + 1)
        halfword = byte0 | (byte1 << 8)
        return halfword
    
    def read_word(self, addr):
        if (addr & 0x3) != 0:
            raise Exception("misaligned word read!")
        byte0 = self.read_byte(addr)
        byte1 = self.read_byte(addr + 1)
        byte2 = self.read_byte(addr + 2)
        byte3 = self.read_byte(addr + 3)
        word = byte0 | (byte1 << 8) | (byte2 << 16) | (byte3 << 24)
        return word
    
    def fetch(self): 
        """
        Gets the next instruction of the loaded program
        """
        return self.instructions[self.pc // 4]
    
    def decode(self, instr):
        """
        Decodes machine code to an actual rv32i instruction
        Args: 
            instr (int): 32-bit instruction
        Returns:
            dict: a dict that holds the values decoded from the instruction (e.g rs1, imm, ect...) 
        """
        def get_rd(): 
            return ((instr >> 7) & 0x1F)
        def get_rs1(): 
            return ((instr >> 15) & 0x1F)
        def get_rs2(): 
            return ((instr >> 20) & 0x1F)
        def get_rd(): 
            return ((instr >> 7) & 0x1F)
        def get_funct3(): 
            return ((instr >> 12) & 0x7)
        def get_funct7(): 
            return ((instr >> 25) & 0x7F)
        def get_shamt(): 
            return ((instr >> 20) & 0x1F)
        
        def get_imm_ltype_zext(): 
            return ((instr >> 20) & 0xFFF)
        def get_imm_ltype_sext(): 
            return sign_extend((instr >> 20) & 0xFFF, 12)
        def get_imm_itype(): 
            return sign_extend((instr >> 20) & 0xFFF, 12)
        
        def get_imm_utype(): 
            return ((instr >> 12) & 0xF_FFFF)

        def get_imm_stype(): 
            imm11_5 = (instr >> 25) & 0x7F
            imm4_0 = (instr >> 7) & 0x1F
            imm = (imm11_5 << 5) | imm4_0
            imm = sign_extend(imm, 12)
            return imm
        
        def get_imm_jal(): 
            imm20    = (instr >> 31) & 0x1
            imm10_1  = (instr >> 21) & 0x3FF
            imm11    = (instr >> 20) & 0x1
            imm19_12 = (instr >> 12) & 0xFF
            # Reassemble into 21-bit immediate and shift left by 1 (only here!)
            imm = (imm20 << 20) | (imm19_12 << 12) | (imm11 << 11) | (imm10_1 << 1)

            sign_extend(imm, 21)
            return imm
        
        def get_imm_btype(): 
            imm12 = (instr >> 31) & 0x1
            imm11 = (instr >> 7) & 0x1
            imm10_5 = (instr >> 25) & 0x3F
            imm4_1 = (instr >> 8) & 0xF
            imm = (imm12 << 12) | (imm11 << 11) | (imm10_5 << 5) | (imm4_1 << 1)

            sign_extend(imm, 12)
            return imm
        
        def get_opcode(): return (instr & 0x7F)
        def get_itype(instr_name): 
            return {
                "op": instr_name,
                "instr_type": "i",
                "rd": get_rd(),
                "rs1": get_rs1(),
                "imm": get_imm_itype()
            }
        def get_itype_shift(instr_name): 
            return {
                "op": instr_name,
                "instr_type": "i_shift",
                "rd": get_rd(),
                "rs1": get_rs1(),
                "shamt": get_shamt()
            }
        def get_rtype(instr_name): 
            return {
                "op": instr_name,
                "instr_type": "r",
                "rd": get_rd(),
                "rs1": get_rs1(),
                "rs2": get_rs2()
            }
        def get_ltype(instr_name, is_sext_imm): 
            if is_sext_imm:
                imm = get_imm_ltype_sext()
            else:
                imm = get_imm_ltype_zext()
            return {
                "op": instr_name,
                "instr_type": "load",
                "rd": get_rd(),
                "rs1": get_rs1(),
                "imm": imm
            }
        def get_stype(instr_name): 
            return {
                "op": instr_name,
                "instr_type": "store",
                "rd": get_rd(),
                "rs1": get_rs1(),
                "rs2": get_rs2(),
                "imm": get_imm_stype()
            }
        def get_btype(instr_name): 
            return {
                "op": instr_name,
                "instr_type": "branch",
                "rs1": get_rs1(),
                "rs2": get_rs2(),
                "imm": get_imm_btype()
            }

        opcode = get_opcode()
        match opcode:
            case 0x03: # L-type instruction
                match get_funct3():
                    case 0x0:
                        return get_ltype("lb", True)
                    case 0x1:
                        return get_ltype("lh", True)
                    case 0x2:
                        return get_ltype("lw", True)
                    case 0x4:
                        return get_ltype("lbu", False)
                    case 0x5:
                        return get_ltype("lhu", False)
            case 0x23:
                match get_funct3():
                    case 0x0:
                        return get_stype("sb")
                    case 0x1:
                        return get_stype("sh")
                    case 0x2:
                        return get_stype("sw")
            case 0x37: # lui instruction
                return {
                    "op": "lui",
                    "instr_type": "u",
                    "rd": get_rd(),
                    "imm": get_imm_utype()
                }
            case 0x17: # auipc instruction
                return {
                    "op": "auipc",
                    "instr_type": "u",
                    "rd": get_rd(),
                    "imm": get_imm_utype()
                }
            case 0x33: # R-type instruction
                match get_funct3():
                    case 0x0:
                        match get_funct7():
                            case 0x0:
                                return get_rtype("add")
                            case 0x20:
                                return get_rtype("sub")
                    case 0x1:
                        return get_rtype("sll")
                    case 0x2:
                        return get_rtype("slt")
                    case 0x3:
                        return get_rtype("sltu")
                    case 0x4:
                        return get_rtype("xor")
                    case 0x5:
                        match get_funct7():
                            case 0x0:
                                return get_rtype("srl")
                            case 0x20:
                                return get_rtype("sra")
                        return get_rtype("sltu")
                    case 0x6:
                        return get_rtype("or")
                    case 0x7:
                        return get_rtype("and")
            case 0x13: # I-type instruction
                match get_funct3():
                    
                    case 0x0:
                        return get_itype("addi")
                    case 0x1: # left shift op
                        return get_itype_shift("slli")
                    case 0x2:
                        return get_itype("slti")
                    case 0x3:
                        return get_itype("sltiu")
                    case 0x4:
                        return get_itype("xori")
                    case 0x6:
                        return get_itype("ori")
                    case 0x7:
                        return get_itype("andi")
                    case 0x5: # right shift op
                        match get_funct7():
                            case 0x0:
                                return get_itype_shift("srli")
                            case 0x20:
                                return get_itype_shift("srai")
            case 0x67: # jalr
                return {
                    "op": "jalr",
                    "instr_type": "jump",
                    "rd": get_rd(),
                    "rs1": get_rs1(),
                    "imm": get_imm_itype()  
                }
            case 0x63: # B-type instruction
                match get_funct3():
                    case 0x0:
                        return get_btype("beq")
                    case 0x1:
                        return get_btype("bne")
                    case 0x4:
                        return get_btype("blt")
                    case 0x5:
                        return get_btype("bge")
                    case 0x6:
                        return get_btype("bltu")
                    case 0x7:
                        return get_btype("bgeu")

            case 0x6F: # jal
                return {
                    "op": "jal",
                    "instr_type": "jump",
                    "rd": get_rd(),
                    "imm": get_imm_jal()  
                }
            case 0x73: # environment instructions
                if (instr & 0xFFFF_FF80) == 0:  # ecall
                    return {
                        "op": "ecall",
                        "instr_type": "environment",  
                    }

    def execute(self, instr_dict: dict):
        """
        Executes the fetched instruction
        """
        op = instr_dict.get('op')
        instr_type = instr_dict.get('instr_type')
        match instr_type:
            case "i":
                self.exec_itype(instr_dict)
            case "i_shift":
                self.exec_itype_shift(instr_dict)
            case "r":
                self.exec_rtype(instr_dict)
            case "load":
                self.exec_ltype(instr_dict)
            case "u":
                self.exec_utype(instr_dict)
            case "store":
                self.exec_stype(instr_dict)
            case "jump":
                self.exec_jtype(instr_dict)
            case "branch":
                self.exec_btype(instr_dict)
            case "environment":
                self.is_halted = True
            case _:
                raise Exception(f"Unknown instruction: {op}, instr_type: {instr_type}")
    
    # INSTRUCTION EXECUTE FUNCTIONS
    
    def exec_itype(self, instr_dict: dict):
        """
        Executes an I-type instruction, not including I-type shifts
        """
        rd = instr_dict.get("rd")
        imm = instr_dict.get("imm")
        rs1 = instr_dict.get("rs1")
        # specific I-type instruction

        itype_ops = {
            "addi":  lambda a, b: a + b,
            "slti":  lambda a, b: 1 if (reinterpret_signed(a, 32) < reinterpret_signed(b, 32)) else 0,
            "sltiu":  lambda a, b: 1 if (reinterpret_unsigned(a, 32) < reinterpret_unsigned(b, 32)) else 0,
            "xori":  lambda a, b: a ^ b,
            "ori": lambda a, b: a | b,
            "andi": lambda a, b: a & b,
            "slli": lambda a, b: reinterpret_signed(a, 32) >> (b & 0x1F),
            "srli": lambda a, b: reinterpret_signed(a, 32) >> (b & 0x1F),
            "srai": lambda a, b: a | b,
        }
        op = instr_dict.get('op')
        calc = itype_ops.get(op)
        if calc:
            write_value = calc(self.read_reg(rs1), imm)
        else:
            raise Exception(f'Unknown instruction! {op}')
        self.write_reg(rd, write_value)
        self.incr_pc()

    def exec_itype_shift(self, instr_dict: dict):
        """
        Executes an I-type shift instruction
        """
        rd = instr_dict.get("rd")
        rs1 = instr_dict.get("rs1")
        shamt = instr_dict.get("shamt") # only exists for shift instructions
        itype_shift_ops = {
            "slli": lambda a, b: a << b,
            "srli": lambda a, b: a >> b,
            "srai": lambda a, b: reinterpret_signed(a, 32) >> b,
        }
        op = instr_dict.get('op')
        calc = itype_shift_ops.get(op)
        if calc:
            write_value = calc(self.read_reg(rs1), shamt)
        else:
            raise Exception(f'Unknown instruction! {op}')
        self.write_reg(rd, write_value)
        self.incr_pc()

    def exec_rtype(self, instr_dict: dict):
        """
        Executes an R-type instruction
        """
        rd = instr_dict.get("rd")
        rs2 = instr_dict.get("rs2")
        rs1 = instr_dict.get("rs1")
        # specific R-type instruction
        rtype_ops = {
            "add":  lambda a, b: a + b,
            "sub":  lambda a, b: a - b,
            "sll":  lambda a, b: a << (b & 0x1F),
            "slt":  lambda a, b: 1 if (reinterpret_signed(a, 32) < reinterpret_signed(b, 32)) else 0,
            "sltu": lambda a, b: 1 if (reinterpret_unsigned(a, 32) < reinterpret_unsigned(b, 32)) else 0,
            "xor": lambda a, b: a ^ b,
            "srl": lambda a, b: reinterpret_unsigned(a, 32) >> (b & 0x1F),
            "sra": lambda a, b: reinterpret_signed(a, 32) >> (b & 0x1F),
            "or": lambda a, b: a | b,
            "and": lambda a, b: a & b,
        }
        op = instr_dict.get('op')
        calc = rtype_ops.get(op)
        if calc:
            write_value = calc(self.read_reg(rs1), self.read_reg(rs2))
        else:
            raise Exception(f'Unknown instruction! {op}')
        self.write_reg(rd, write_value)
        self.incr_pc()

    def exec_ltype(self, instr_dict: dict):
        """
        Executes a load-type instruction
        """
        rd = instr_dict.get("rd")
        offset = instr_dict.get("imm")
        rs1 = instr_dict["rs1"]
        # specific Load-type instruction
        match instr_dict.get('op'):
            case "lb":
                write_value = sign_extend(self.read_byte(self.read_reg(rs1) + offset), 32)
            case "lh":
                write_value = sign_extend(self.read_halfword(self.read_reg(rs1) + offset), 32)
            case "lw":
                write_value = sign_extend(self.read_word(self.read_reg(rs1) + offset), 32)
            case "lbu":
                write_value = self.read_byte(self.read_reg(rs1) + offset)
            case "lhu":
                write_value = self.read_halfword(self.read_reg(rs1) + offset)
        self.write_reg(rd, write_value)
        self.incr_pc()

    def exec_utype(self, instr_dict: dict):
        """
        Executes a U-type instruction
        """
        rd = instr_dict.get('rd')
        imm = instr_dict.get('imm')
        # specific U-type instruction
        match instr_dict.get('op'):
            case "lui":
                write_value = sign_extend((imm << 12), 32)
            case "auipc":
                write_value = sign_extend((imm << 12), 32) + self.pc
        self.write_reg(rd, write_value)
        self.incr_pc()

    def exec_stype(self, instr_dict: dict):
        """
        Executes a store-type instruction
        """
        offset = instr_dict.get('imm')
        rs1 = instr_dict.get('rs1')
        rs2 = instr_dict.get('rs2')
        # specific store-type instruction
        memory_addr = self.read_reg(rs1) + offset
        match instr_dict.get('op'):
            case "sb":
                write_data = self.read_reg(rs2) & 0xFF
                self.write_byte(memory_addr, write_data)
            case "sh":
                write_data = self.read_reg(rs2) & 0xFFFF
                self.write_halfword(memory_addr, write_data)
            case "sw":
                write_data = self.read_reg(rs2)
                self.write_word(memory_addr, write_data)
        self.incr_pc()
    
    def exec_jtype(self, instr_dict: dict):
        """
        Executes a jump-type instruction
        """
        rd = instr_dict.get('rd')
        offset = instr_dict.get('imm')
        match instr_dict.get('op'):
            case "jal":
                self.write_reg(rd, self.pc + 4)
                self.incr_pc(offset)
            case "jalr":
                rs1 = instr_dict["rs1"]
                t = self.pc + 4
                self.set_pc((self.read_reg(rs1) + offset) & ~1)
                self.write_reg(rd, t)
    
    def exec_btype(self, instr_dict: dict):
        """
        Executes a branch-type instruction
        """
        offset = instr_dict.get('imm')
        rs2 = instr_dict.get('rs2')
        rs1 = instr_dict.get('rs1')

        branch_ops = {
            "beq":  lambda a, b: a == b,
            "bne":  lambda a, b: a != b,
            "blt":  lambda a, b: reinterpret_signed(a, 32) < reinterpret_signed(b, 32),
            "bge":  lambda a, b: reinterpret_signed(a, 32) >= reinterpret_signed(b, 32),
            "bltu": lambda a, b: a < b,
            "bgeu": lambda a, b: a >= b,
        }
        op = instr_dict.get('op')
        cond = branch_ops.get(op)

        if cond and cond(self.read_reg(rs1), self.read_reg(rs2)):
            self.incr_pc(offset)
        else:
            self.incr_pc()