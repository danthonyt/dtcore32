import cocotb
from cocotb.triggers import FallingEdge,ClockCycles
from cocotb.queue import QueueEmpty, Queue
import logging
import pyuvm




# #### The uart_prediction function
# The prediction function for the scoreboard
def uart_prediction(input_tx_data,input_rx_uart_payload):
    """Python model of the uart"""
    # received data will be output to a data bus
    # 8 bit value (without start and stop bit)
    # we do not reverse the data byte since our uart
    # outputs the data byte MSB first 
    output_rx_data = int(f'{((input_rx_uart_payload>>1) &0xFF):08b}'[::-1],2)
    # transmitted data will be output serially
    # reverse the data byte since our uart transmits data LSB first
    # 10 bit value (with start and stop bit) 
    output_tx_uart_payload = (int(f'{input_tx_data:08b}'[::-1],2) << 1) & ~(1 << 9) | 1
    results_tuple = (output_tx_uart_payload, output_rx_data)
    return results_tuple



# #### The logger

# Setting up logging using the logger variable
logging.basicConfig(level=logging.NOTSET)
logger = logging.getLogger()
logger.setLevel(logging.DEBUG)

# uart message and data bus formatting function
def format_uart_bus(input_bus):
    return f"{(input_bus>> 4 & 0x0F):04b}_{(input_bus>> 0 & 0x0F):04b}"
def format_uart_msg(input_msg):
    return f"{(input_msg >> 9 & 0x01):01b}_{(input_msg >> 5 & 0x0F):04b}_{(input_msg >> 1 & 0x0F):04b}_{(input_msg >> 0 & 0x01):01b}"

# ### Reading a signal value
# get_int() converts a bus to an integer
# turning a value of x or z to 0
def get_int(signal):
    try:
        int_val = int(signal.value)
    except ValueError:
        int_val = 0
    return int_val

# ## The uartBfm singleton
# ### Initializing the uartBfm object


# Initializing the uartBfm singleton
class uartBfm(metaclass=pyuvm.Singleton):
    def __init__(self):
        self.dut = cocotb.top
        self.cmd_driver_queue = Queue(maxsize=1)
        self.cmd_mon_queue = Queue(maxsize=0)
        self.result_mon_queue = Queue(maxsize=0)

# ### The reset coroutine

# Centralizing the reset function
    async def reset(self):
        await FallingEdge(self.dut.clk)
        self.dut.reset.value = 1
        await FallingEdge(self.dut.clk)
        self.dut.reset.value = 0
        await FallingEdge(self.dut.clk)

# ## The communication coroutines
# #### result_mon()

# Monitoring the result bus
    async def result_mon(self):
        while True:
            await FallingEdge(self.dut.clk)
            start = get_int(self.dut.start)
            if start == 1:
                await FallingEdge(self.dut.clk)
                # sample all bits transmitted
                # find middle of start bit
                await ClockCycles(self.dut.clk,44,False)
                # sample start bit to stop bit transmitted
                output_tx_uart_payload = 0
                for index in range(10):
                    output_tx_uart_payload = output_tx_uart_payload | (get_int(self.dut.serial_tx )<<(9-index))
                    # move to next bit
                    if index < 9:
                        await ClockCycles(self.dut.clk,87,False)
                result_tuple = (output_tx_uart_payload, get_int(self.dut.dout_rx))
                self.result_mon_queue.put_nowait(result_tuple)

# #### cmd_mon()
# Monitoring the command signals
    async def cmd_mon(self):
        while True:
            await FallingEdge(self.dut.clk)
            start = get_int(self.dut.start)
            if start == 1:
                # sample all bits transmitted
                # find middle of start bit
                await ClockCycles(self.dut.clk,44,False)
                # sample start bit to stop bit transmitted
                input_rx_uart_payload = 0
                for index in range(10):
                    input_rx_uart_payload |= (get_int(self.dut.serial_rx )<<(9-index))
                    # move to next bit
                    if index < 9:
                        await ClockCycles(self.dut.clk,87,False)
                cmd_tuple = (get_int(self.dut.din_tx), input_rx_uart_payload)
                self.cmd_mon_queue.put_nowait(cmd_tuple)

# #### driver()
# Driving commands on the falling edge of clk
    async def cmd_driver(self):
        self.dut.start.value = 0
        self.dut.serial_rx.value = 1
        self.dut.din_tx.value = 0
        while True:
            await FallingEdge(self.dut.clk)
            st = get_int(self.dut.start)
            dn = get_int(self.dut.done)
# Driving commands to the uartBfm when
# start and done are 0
            if st == 0 and dn == 0:
                try:
                    # cmd is transmit data and and receive data 
                    (input_tx_data, input_rx_uart_payload) = self.cmd_driver_queue.get_nowait()
                    self.dut.start.value = 1
                    # drive tx input data for Tx.
                    self.dut.din_tx.value = input_tx_data
                    await FallingEdge(self.dut.clk)
                    self.dut.start.value = 0
                    # drive start bit to stop bit received
                    for index in range(10):
                        self.dut.serial_rx.value = ((input_rx_uart_payload >> (9-index)) & 1)
                        await ClockCycles(self.dut.clk,87,False)
                except QueueEmpty:
                    continue

# ### Launching the coroutines using start_soon
# Start the BFM coroutines
    def start_tasks(self):
        cocotb.start_soon(self.cmd_driver())
        cocotb.start_soon(self.cmd_mon())
        cocotb.start_soon(self.result_mon())

# The get_cmd() coroutine returns the next command
    async def get_cmd(self):
        cmd = await self.cmd_mon_queue.get()
        return cmd

# The get_result() coroutine returns the next result
    async def get_result(self):
        result = await self.result_mon_queue.get()
        return result

# send_op puts the command into the command Queue
    async def send_op(self, input_tx_data,input_rx_uart_payload):
        command_tuple = (input_tx_data,input_rx_uart_payload)
        await self.cmd_driver_queue.put(command_tuple)