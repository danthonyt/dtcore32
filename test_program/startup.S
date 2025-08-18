    .section .text.reset
    .globl _start
_start:
    /* initialize sp from linker symbol _stack_top */
    la   sp, _stack_top

    /* optional: zero .bss (if you have globals) */
    la   t0, __bss_start
    la   t1, __bss_end
    beq  t0, t1, 1f
0:
    sw   x0, 0(t0)
    addi t0, t0, 4
    blt  t0, t1, 0b
1:

    /* call main */
    call main

/* hang */
1:  j 1b

    /* symbols expected by linker (if using .data/.bss) */
    .weak __bss_start
    .weak __bss_end
    .size _start, .-_start
