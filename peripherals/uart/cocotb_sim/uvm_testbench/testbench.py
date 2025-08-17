from cocotb.triggers import Combine
from pyuvm import *
import random
import pyuvm
import cocotb
import sys 
from pathlib import Path
sys.path.insert(0, str(Path("..").resolve()))
from uart_utils import uartBfm, uart_prediction, format_uart_msg, format_uart_bus

# Launching sequences from a virtual sequence
# Calling a virtual sequence
@pyuvm.test()
class UartTest(uvm_test):
    def build_phase(self):
        self.env = UartEnv("env",self)

    def end_of_elaboration_phase(self):
        self.test_all = TestAllSeq.create("test_all")

    async def run_phase(self):
        self.raise_objection()
        await self.test_all.start()
        self.drop_objection()

# A virtual sequence starts other sequences
class TestAllSeq(uvm_sequence):

    async def body(self):
        seqr = ConfigDB().get(None,"","SEQR")
        random_seq = RandomSeq("random")
        max_seq = MaxSeq("max")
        await random_seq.start(seqr)
        await max_seq.start(seqr)

# Running RandomSeq and MaxSeq in parallel
class TestAllParallelSeq(uvm_sequence):

    async def body(self):
        seqr = ConfigDB().get(None,"","SEQR")
        random_seq = RandomSeq("random")
        max_seq = MaxSeq("max")
        random_task = cocotb.start_soon(random_seq.start(seqr))
        max_task = cocotb.start_soon(max_seq.start(seqr))
        await Combine(random_task,max_task)

# Defining the Uart Command as a sequence item
class UartSeqItem(uvm_sequence_item):

    def __init__(self,name,tx,rx):
        super().__init__(name)
        self.input_tx_data = tx
        self.input_rx_uart_payload = rx
        #self.op = Ops(op)
    
    def __eq__(self,other):
        same = self.input_tx_data == other.input_tx_data and self.input_rx_uart_payload == other.input_rx_uart_payload
        # and self.op == other.op
        return same
    
    def __str__(self):
        return f"{self.get_name()}:T:{format_uart_bus(self.input_tx_data)}\
            R:{format_uart_msg(self.input_rx_uart_payload)}"
        '''
        return f"{self.get_name()}:T:0x{format_uart_bus(self.T)}\
            Op:{self.op.name}({self.op.value})R:{format_uart_msg(self.input_rx_uart_payload)}"
        '''

class BaseSeq(uvm_sequence):

    async def body(self):
        '''
        for op in list(Ops):
            cmd_tr = UartSeqItem("cmd_tr",0,0,op)
            await self.start_item(cmd_tr)
            self.set_operands(cmd_tr)
            await self.finish_item(cmd_tr)
        '''
        cmd_tr = UartSeqItem("cmd_tr",0,0)
        await self.start_item(cmd_tr)
        self.set_operands(cmd_tr)
        await self.finish_item(cmd_tr)

    def set_operands(self,tr):
        pass


class RandomSeq(BaseSeq):

    def set_operands(self, tr):
        tr.input_tx_data = random.randint(0,255)
        tr.input_rx_uart_payload = (random.randint(0,255)<<1) & ~(1<<9)|(1)


class MaxSeq(BaseSeq):

    def set_operands(self, tr):
        tr.input_tx_data = 0xFF
        tr.input_rx_uart_payload = (0xFF<<1) & ~(1<<9)|(1)


class Driver(uvm_driver):
    def build_phase(self):
        self.ap = uvm_analysis_port("ap",self)

    def start_of_simulation_phase(self):
        self.bfm = uartBfm()
    
    async def launch_tb(self):
        await self.bfm.reset()
        self.bfm.start_tasks()

    async def run_phase(self):
        await self.launch_tb()
        while True:
            cmd = await self.seq_item_port.get_next_item()
            await self.bfm.send_op(cmd.input_tx_data,cmd.input_rx_uart_payload)
            result = await self.bfm.get_result()
            self.ap.write(result)
            cmd.result = result
            self.seq_item_port.item_done()


'''
# class for coverage
class Coverage(uvm_analysis_export):

    def start_of_simulation_phase(self):
        self.cvg = set()


    def write(self,cmd):
        _,_,op = cmd
        self.cvg.add(Ops(op))

    def check_phase(self):
        if len(set(Ops) - self.cvg) > 0:
            self.logger.error(
                f"Functional coverage error. Missed: {set(Ops)-self.cvg}")
            assert False
        else:
            self.logger.info("Covered all operations")
'''
        

class Scoreboard(uvm_component):

    def build_phase(self):
        self.cmd_fifo = uvm_tlm_analysis_fifo("cmd_fifo",self)
        self.result_fifo = uvm_tlm_analysis_fifo("result_fifo",self)
        self.cmd_get_port = uvm_get_port("cmd_get_port",self)
        self.result_get_port = uvm_get_port("result_get_port",self)
        self.cmd_export = self.cmd_fifo.analysis_export
        self.result_export = self.result_fifo.analysis_export

    def connect_phase(self):
        self.cmd_get_port.connect(self.cmd_fifo.get_export)
        self.result_get_port.connect(self.result_fifo.get_export)
        
    def check_phase(self):
        while self.result_get_port.can_get():
            _, actual_result = self.result_get_port.try_get()
            cmd_success, cmd = self.cmd_get_port.try_get()
            if not cmd_success:
                self.logger.critical(f"result {actual_result} had no command")
            else:
                (input_tx_data, input_rx_uart_payload) = cmd
                predicted_result = uart_prediction(input_tx_data,input_rx_uart_payload)
                if actual_result == predicted_result:
                    self.logger.info(   f"PASSED: INPUT TX DATABUS : " + format_uart_bus(input_tx_data) + " "
                                        f"INPUT RX MSG : " + format_uart_msg(input_rx_uart_payload) + " => "
                                        f"OUTPUT TX MSG : " + format_uart_msg(actual_result[0]) + " "
                                        f"OUTPUT RX DATABUS : " + format_uart_bus(actual_result[1]) + " "
                                    )
                else:
                    self.logger.error(   f"FAILED: 8 bit input tx_din : {input_tx_data:08b}  10 bit input rx_msg : {input_rx_uart_payload:010b} "
                                    f'= 10 bit output tx_msg : {actual_result[0]:010b} - predicted : {predicted_result[0]:010b}'
                                    f' 8 bit output rx_dout : {actual_result[1]:08b} - predicted : {predicted_result[1]:08b}')


class Monitor(uvm_monitor):

    def __init__(self, name, parent, method_name):
        super().__init__(name, parent)
        self.bfm = uartBfm()
        self.get_method = getattr(self.bfm,method_name)

    def build_phase(self):
        self.ap = uvm_analysis_port("ap",self)
        
    async def run_phase(self):
        while True:
            datum = await self.get_method()
            self.logger.debug(f"MONITORED {datum}")
            self.ap.write(datum)


class UartEnv(uvm_env):
    
    def build_phase(self):
        self.seqr = uvm_sequencer("seqr",self)
        ConfigDB().set(None,"*","SEQR",self.seqr)
        self.driver = Driver("driver",self)
        self.scoreboard = Scoreboard("scoreboard",self)
        #self.coverage = Coverage("coverage",self)
        self.cmd_mon = Monitor("cmd_monitor",self,"get_cmd")

    def connect_phase(self):
        self.driver.seq_item_port.connect(self.seqr.seq_item_export)
        #self.cmd_mon.ap.connect(self.coverage.analysis_export)
        self.cmd_mon.ap.connect(self.scoreboard.cmd_export)
        self.driver.ap.connect(self.scoreboard.result_export)


@pyuvm.test()
class ParallelTest(UartTest):
    def end_of_elaboration_phase(self):
        uvm_factory().set_type_override_by_type(TestAllSeq,TestAllParallelSeq)
        return super().end_of_elaboration_phase()