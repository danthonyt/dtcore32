CWD=$(shell pwd)
COCOTB_REDUCED_LOG_FMT = True
SIM ?= icarus
VERILOG_SOURCES = 	$(CWD)/../../rtl/uart_tx.sv \
					$(CWD)/../../rtl/uart_rx.sv \
					$(CWD)/../../rtl/uart_top.sv 	
MODULE := testbench
TOPLEVEL := uart_top
TOPLEVEL_LANG := verilog
COCOTB_HDL_TIMEUNIT=1us
COCOTB_HDL_TIMEPRECISION=1us
include $(shell cocotb-config --makefiles)/Makefile.sim
#include ../cleanall.mk
