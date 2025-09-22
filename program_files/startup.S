    .section .text
    .globl _start
    .globl trap_vector

_start:
    la sp, _stack_start      # set stack pointer
    call main                # jump to main program

    # Infinite loop after main returns
1:  j 1b

# --- Trap vector ---
    .align 4
    .globl trap_vector
trap_vector:
    addi sp, sp, -16         # reserve space for x registers if needed
    sw   ra, 12(sp)
    sw   t0, 8(sp)
    sw   t1, 4(sp)
    sw   t2, 0(sp)

    la a0, mcause_val        # pointer to store mcause temporarily
    csrr t0, mcause
    sw   t0, 0(a0)

    call trap_handler        # call C handler

    # hang forever
hang:
    j hang
