#include <stdint.h>

static volatile uint32_t * const UART_TX_FIFO  = (uint32_t *)0x01000004;
static volatile uint32_t * const UART_STAT_REG = (uint32_t *)0x01000008;
static volatile uint32_t * const UART_CTRL_REG = (uint32_t *)0x0100000C;
static const uint32_t TX_FIFO_FULL  = 0x8;
static const uint32_t TX_FIFO_EMPTY = 0x4;
static const uint32_t RST_TX_FIFO   = 0x1;
static const uint32_t IRQ_EN        = 0x10;

// --- UART functions ---
void uart_putc(char c) {
    while (*UART_STAT_REG & TX_FIFO_FULL);  // wait if FIFO full
    *UART_TX_FIFO = (uint32_t)c;
}

void uart_tx_init(void) {
    // reset tx fifo
    // disable interrupts
    *UART_CTRL_REG = *UART_CTRL_REG | (RST_TX_FIFO) & ~(IRQ_EN);
    

}

void uart_puts(const char *s) {
    while (*s) {
        if (*s == '\n') {
            uart_putc('\r'); // carriage return
            uart_putc('\n'); // newline
        } else {
            uart_putc(*s);
        }
        s++;
    }
}


void uart_putu32(uint32_t v) {
    char buf[11];  // enough for 32-bit decimal
    int i = 10;
    buf[i] = '\0';
    if (v == 0) {
        buf[--i] = '0';
    } else {
        while (v) {
            buf[--i] = '0' + (v % 10);
            v /= 10;
        }
    }
    uart_puts(&buf[i]);
}

// --- Main ---
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
