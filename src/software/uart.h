#ifndef UART_H
#define UART_H

#include <stdint.h>

// UART API
void uart_tx_init(void);
void uart_putc(char c);
void uart_puts(const char *s);
void uart_putu32(uint32_t v);

#endif // UART_H
