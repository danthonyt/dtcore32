#include <stdint.h>

#define UART_RX_FIFO   (*(volatile uint32_t *)(0x01000000))
#define UART_TX_FIFO   (*(volatile uint32_t *)(0x01000004))
#define UART_STAT_REG  (*(volatile uint32_t *)(0x01000008))

// These might need adjustment based on your UART datasheet
#define RX_VALID       0x1   // bit high when data available
#define TX_FIFO_FULL   0x8   // bit high when TX full
#define TX_FIFO_EMPTY  0x4   // bit high when TX empty

#define BUF_SIZE 64

char rx_buf[BUF_SIZE];

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

// Non-blocking receive with optional timeout
int uart_getc_nb(char *c) {
    // simple timeout counter
    volatile int timeout = 1000000;
    while (!(UART_STAT_REG & RX_VALID)) {
        if (--timeout == 0) return 0; // no data
    }
    *c = (char)(UART_RX_FIFO & 0xFF);
    return 1; // success
}

// Blocking receive wrapper
char uart_getc(void) {
    char c;
    while (!uart_getc_nb(&c));
    return c;
}

// --- Main echo loop ---
int main(void) {
    uart_puts("UART Test\r\n");
    uart_flush();

    while (1) {
        char c = uart_getc();   // wait for a character
        uart_putc(c);           // echo it back
    }
}
