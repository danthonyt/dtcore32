.section .text
.globl _start
.globl main
.globl __bss_start
.globl __bss_end
.globl _stack_end


_start:
    la sp, _stack_end          # initialize stack

    la t0, __bss_start         # zero BSS
    la t1, __bss_end
    li t2, 0
bss_clear:
    bge t0, t1, bss_done
    sw t2, 0(t0)
    addi t0, t0, 4
    j bss_clear
bss_done:

    call main                  # jump to main

hang:
    j hang
