#include <stdint.h>
#include "uart.h"

// Memory-mapped UART registers
static volatile uint32_t * const UART_STATUS_REG  = (uint32_t *)0x01000000;
static volatile uint32_t * const UART_CTRL_REG  = (uint32_t *)0x01000004;
static volatile uint32_t * const UART_RX_FIFO = (uint32_t *)0x01000008;
static volatile uint32_t * const UART_TX_FIFO = (uint32_t *)0x0100000C;

// UART flags
static const uint32_t RX_FIFO_FULL  = 0x1;
static const uint32_t RX_FIFO_EMPTY = 0x2;
static const uint32_t TX_FIFO_FULL  = 0x4;
static const uint32_t TX_FIFO_EMPTY = 0x8;
static const uint32_t RST_RX_FIFO   = 0x1;
static const uint32_t RST_TX_FIFO   = 0x2;

// --- UART functions ---
void uart_putc(char c) {
    while (*UART_STATUS_REG & TX_FIFO_FULL);  // wait if FIFO full
    *UART_TX_FIFO = (uint32_t)c;
   //while (!(*UART_STATUS_REG & TX_FIFO_EMPTY));  // wait until fifo is empty
}

/*
void uart_tx_init(void) {
    // reset tx fifo 
    //*UART_CTRL_REG = (*UART_CTRL_REG | RST_TX_FIFO);
    //*UART_CTRL_REG = (*UART_CTRL_REG & ~RST_TX_FIFO);
}
    */

void uart_puts(const char *s) {
    while (*s) {
            uart_putc(*s);
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
