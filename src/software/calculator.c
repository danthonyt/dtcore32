#include <stdint.h>
#include "uart.h"

// ---- Replace these with your platform's UART drivers ----


// Convert ASCII '0'..'9' to int
int char_to_int(char c) {
    return c - '0';
}

// Convert int 0..9 to ASCII
char int_to_char(int n) {
    return (char)(n + '0');
}
int32_t get_32int_string(void) {
    char buf[11];  // enough for -2147483648 + '\0'
    int i = 0;
    char c;

    // read characters until Enter (\r or \n)
    while (i < 10) {
        c = uart_getc();
        if (c == '\r' || c == '\n') {
            break;
        }
        buf[i++] = c;
    }

    buf[i] = '\0';  // null terminate

    // convert string to int (simple atoi)
    int32_t val = 0;
    int sign = 1;
    int j = 0;

    if (buf[0] == '-') {  // handle negative
        sign = -1;
        j = 1;
    }

    for (; j < i; j++) {
        val = val * 10 + (buf[j] - '0');
    }

    return val * sign;
}

int main(void) {
    int32_t operand1, operand2;
    char op;
    int32_t a, b, result;

    uart_puts("Baremetal Calculator Ready\n");
    uart_puts("Format: <digit><op><digit>\n");
    uart_puts("Ops: +  -  &  |  ^\n");

    while (1) {
        // read first number
        operand1 = get_32int_string();
        uart_putu32(operand1);

        // read operator
        op = uart_getc();
        uart_putc(op);

        // read second number
        operand2 = get_32int_string();
        uart_putu32(operand2);

        // compute
        switch (op) {
            case '+': result = operand1 + operand2; break;
            case '-': result = operand1 - operand2; break;
            case '&': result = operand1 & operand2; break;
            case '|': result = operand1 | operand2; break;
            case '^': result = operand1 ^ operand2; break;
            default:
                uart_puts("\nInvalid op\n");
                continue;
        }

        // output result (single digit only for now)
        uart_puts(" = ");
        uart_putu32(result);
        uart_puts("\n");
    }
}
