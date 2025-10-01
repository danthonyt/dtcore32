Welcome to DTCore's documentation!
===================================

**DTCore** is a 5-stage pipelined soft CPU Core written in Verilog.
It currently supports the RV32I base ISA version 2.2. It also partially supports the machine mode priveledged ISA, supportion exceptions but
not external interrupts.

Check out the  section for further information, including
how to  the project.

.. note::

   This project is under active development.

Contents
--------

.. toctree::

   pipeline_details
   if_stage
   id_stage
   ex_stage
   mem_stage
   wb_stage
   csr
   hazard_control
