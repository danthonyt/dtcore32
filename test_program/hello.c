#include <stdint.h>

#define UART0_BASE   0x400
#define UART_RX_FIFO   ((volatile uint32_t *)(UART0_BASE + 0))
#define UART_TX_FIFO   ((volatile uint32_t *)(UART0_BASE + 4))
#define UART_STAT_REG  ((volatile uint32_t *)(UART0_BASE + 8))
#define UART_CTRL_REG   ((volatile uint32_t *)(UART0_BASE + 12))
#define TX_FIFO_FULL     0x8
#define TX_DATA          0xff

void uart_putc(char c) {
    // Wait until TX IS NOT FULL
    while (!(*UART_STAT_REG & TX_FIFO_FULL));
    *UART_CTRL_REG = (*UART_CTRL_REG & 0xffffff00) | c;
}

void uart_puts(const char *s) {
    while (*s) {
        uart_putc(*s++);
    }
}

void main() {
    uart_puts("Hello World\n");
    while (1); // Loop forever
}
