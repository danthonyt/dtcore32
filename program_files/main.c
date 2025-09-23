#include <stdint.h>
#include "uart.h"

extern uint32_t my_global;
uint32_t check = 0;

void main() {
    // Copy the value for inspection
    check = my_global;

    uart_putu32(check);
    uart_puts("\n");

    while(1); // hang
}
