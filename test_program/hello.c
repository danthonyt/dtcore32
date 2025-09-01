#include <stdint.h>

#define UART_STATUS_REG   (*(volatile uint32_t *)(0x01000000))
#define UART_TX_FIFO      (*(volatile uint32_t *)(0x0100000C))
#define UART_RX_FIFO      (*(volatile uint32_t *)(0x01000008))

#define TX_FIFO_EMPTY   0x8
#define TX_FIFO_FULL   0x4
#define RX_FIFO_EMPTY  0x2
#define RX_FIFO_FULL  0x1

#define BUF_SIZE 16
char rx_buf[BUF_SIZE];

// --- UART functions ---
void uart_putc(char c) {
    // Wait until TX FIFO has space
    while (UART_STATUS_REG & TX_FIFO_FULL);

    // Write the character
    UART_TX_FIFO = (uint32_t)c;

}

char uart_getc() {
    while (UART_STATUS_REG & RX_FIFO_EMPTY);
    return (char)UART_RX_FIFO;
}

void uart_puts(const char *s) {
    while (*s) {
        if (*s == '\n') uart_putc('\r'); // CR before LF
        uart_putc(*s++);
    }
}

// Convert integer to string and send via UART
void uart_putint(int value) {
    char buf[12];
    int i = 0;

    if (value == 0) {
        uart_putc('0');
        return;
    }

    if (value < 0) {
        uart_putc('-');
        value = -value;
    }

    while (value > 0 && i < sizeof(buf)) {
        buf[i++] = '0' + (value % 10);
        value /= 10;
    }

    while (i > 0) {
        uart_putc(buf[--i]);
    }
}

// --- Parse simple expression (add/sub only) ---
int parse_and_calc(const char *expr, int *res) {
    int i = 0;
    int a = 0, b = 0;

    // parse first number
    while (expr[i] >= '0' && expr[i] <= '9') {
        a = a * 10 + (expr[i++] - '0');
    }

    char op = expr[i++]; // operator

    // parse second number
    while (expr[i] >= '0' && expr[i] <= '9') {
        b = b * 10 + (expr[i++] - '0');
    }

    if (op == '+') *res = a + b;
    else if (op == '-') *res = a - b;
    else return -1; // invalid operator

    return 0;
}

// --- Main calculator loop ---
int main(void) {
    uart_puts("UART Calculator Ready (+ and - only)\n");

    int pos = 0;

    while (1) {
        char c = uart_getc();

        // Enter pressed
        if (c == '\r' || c == '\n') {
            if (pos == 0) continue; // ignore empty lines
            rx_buf[pos] = '\0';

            int result;
            if (parse_and_calc(rx_buf, &result) == 0) {
                uart_puts("=");
                uart_putint(result);
                uart_puts("\r\n");
            } else {
                uart_puts("Error: invalid input\r\n");
            }

            pos = 0; // reset buffer
        } else {
            // only accept digits and +/-
            if ((c >= '0' && c <= '9') || c == '+' || c == '-') {
                if (pos < BUF_SIZE - 1) {
                    uart_putc(c);       // echo immediately
                    rx_buf[pos++] = c;  // store in buffer
                }
            }
        }
    }
}
