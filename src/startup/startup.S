    .section .text
    .globl _start

_start:
    # --- Set up stack ---
    la sp, _stack_start        # _stack_start defined in linker script

    # --- Copy .data from ROM to RAM ---
    la t0, _sdata              # start of .data in RAM
    la t1, _edata              # end of .data
    la t2, _sidata             # start of initial values in ROM
1:  bge t0, t1, 2f
    lw t3, 0(t2)
    sw t3, 0(t0)
    addi t0, t0, 4
    addi t2, t2, 4
    j 1b
2:

    # --- Copy .sdata (small initialized data) from ROM to RAM ---
    la t0, _ssdata             # start of .sdata in RAM
    la t1, _esdata             # end of .sdata
    la t2, _sisddata           # start of initial values in ROM
5:  bge t0, t1, 6f
    lw t3, 0(t2)
    sw t3, 0(t0)
    addi t0, t0, 4
    addi t2, t2, 4
    j 5b
6:

    # --- Clear .bss ---
    la t0, _sbss
    la t1, _ebss
    li t2, 0
3:  bge t0, t1, 4f
    sw t2, 0(t0)
    addi t0, t0, 4
    j 3b
4:

    # --- Call main ---
    call main

hang:
    j hang
