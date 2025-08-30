    .section .text
    .globl _start
    .globl main

_start:
    /* Set stack pointer to top of reserved stack */
    la sp, _stack_end

    /* Zero initialize .bss */
    la   t0, __bss_start   /* start of .bss */
    la   t1, __bss_end     /* end of .bss */
    li   t2, 0

bss_clear:
    bge  t0, t1, bss_done
    sw   t2, 0(t0)
    addi t0, t0, 4
    j    bss_clear
bss_done:

    /* (Optional) Copy .data init values if using AT > IMEM in linker script
       For now we skip this because data lives directly in DMEM */

    /* Jump to main() */
    call main

    /* If main ever returns, just loop forever */
hang:
    j hang

/* Symbols provided by the linker script */
    .section .bss
    .globl __bss_start
    .globl __bss_end
