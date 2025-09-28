#include "uart.h"

int main(void) {
    uart_puts("Hello world! This is a very, very long message that should not be cut off!\n");

    while (1) {
        // halt CPU or idle
    }
}
