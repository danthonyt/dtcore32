#include <stdint.h>

#define UART_RX_FIFO   ((volatile uint32_t *)(0x2400))
#define UART_TX_FIFO   ((volatile uint32_t *)(0x2404))
#define UART_STAT_REG  ((volatile uint32_t *)(0x2408))
#define UART_CTRL_REG  ((volatile uint32_t *)(0x240C))
#define TX_FIFO_FULL   0x8

// Write a single character via a guaranteed 32-bit store
static inline void uart_putc(char c) {
    uint32_t word = (uint32_t)c;  // cast to 32-bit
    // Wait until TX is not full (32-bit read)
    while ((*UART_STAT_REG & TX_FIFO_FULL) != 0) { }
    // 32-bit write to TX FIFO
    *UART_TX_FIFO = word;
}

// Write a string using 32-bit stores
static inline void uart_puts(const char *s) {
    while (*s) {
        uart_putc(*s++);
    }
}

void main() {
    uart_puts("Hello World\n");
    while (1); // loop forever
}
