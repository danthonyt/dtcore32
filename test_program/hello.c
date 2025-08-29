#include <stdint.h>

#define UART_STATUS_REG  ((volatile uint32_t *)(0x01000000))
#define UART_CONTROL_REG   ((volatile uint32_t *)(0x01000004))
#define UART_RX_FIFO  ((volatile uint32_t *)(0x01000008))
#define UART_TX_FIFO  ((volatile uint32_t *)(0x0100000C))
#define TX_FIFO_FULL   0x4
#define RX_FIFO_FULL   0x1
#define TX_FIFO_EMPTY   0x8
#define RX_FIFO_EMPTY   0x2

// Write a single character via a guaranteed 32-bit store
static inline void uart_putc(char c) {
    uint32_t word = (uint32_t)c;  // cast to 32-bit
    // Wait until TX is not full (32-bit read)
    while ((*UART_STATUS_REG & TX_FIFO_FULL) != 0) { }
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
