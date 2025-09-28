#include <stdint.h>

#include "uart.h"

volatile uint32_t mcause_val;

void trap_handler(void) __attribute__((section(".trap")));
void trap_handler(void) {
    uart_puts("TRAP! mcause = ");
    uart_putu32(mcause_val);     // print the cause code
    uart_puts("\n");

    while(1);                    // hang forever
}
