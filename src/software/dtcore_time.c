#include "dtcore_time.h"
uint32_t timer_get_cycles(void)
{
    volatile uint32_t cycles;
    asm volatile("csrr %0, mcycle" : "=r"(cycles));
    return cycles;
}