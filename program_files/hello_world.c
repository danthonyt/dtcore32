#include "uart.h"

int main(void) {
    uart_tx_init();
    uart_puts("Before multiply\n");

    volatile uint32_t a = 12345;
    volatile uint32_t b = 67890;
    volatile uint32_t result;
    result = a * b;  // triggers __mulsi3

    uart_puts("After multiply, result: ");
    uart_putu32(result);
    uart_puts("\n");

    uart_puts("Hello world! This is a long message\n");

    while (1) {
        // halt CPU or idle
    }
}
