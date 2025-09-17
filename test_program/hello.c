#include <stdint.h>

#define UART_TX_FIFO   (*(volatile uint32_t *)(0x01000004))
#define UART_STAT_REG  (*(volatile uint32_t *)(0x01000008))

#define TX_FIFO_FULL   0x8   // bit high when TX full
#define TX_FIFO_EMPTY  0x4   // bit high when TX empty

// --- UART functions ---
void uart_putc(char c) {
    while (UART_STAT_REG & TX_FIFO_FULL);  // wait if FIFO full
    UART_TX_FIFO = (uint32_t)c;
    for (volatile int i = 0; i < 100; i++); // small delay
}

void uart_puts(const char *s) {
    while (*s) uart_putc(*s++);
}

void uart_flush(void) {
    while ((UART_STAT_REG & TX_FIFO_EMPTY) == 0);
    for (volatile int i = 0; i < 100; i++);
}

// --- Main ---
int main(void) {
    uart_puts("Hello, World!\r\n");
    uart_flush();

    while (1) {
        // do nothing, or optionally halt CPU
    }
}
