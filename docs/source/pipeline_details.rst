RISC-V Pipeline Documentation
=============================

Overview
--------

This document explains the 5-stage pipeline of the RISC-V RV32I core.  
Each section covers one stage of the pipeline, describing its purpose, signals,  
and example Verilog implementation.

Pipeline Stages
---------------

The core pipeline consists of the following stages:

1. :ref:`if_stage`
2. :ref:`id_stage`
3. :ref:`ex_stage`
4. :ref:`mem_stage`
5. :ref:`wb_stage`

.. toctree::
   :maxdepth: 1
   :caption: Pipeline Stages

   if_stage
   id_stage
   ex_stage
   mem_stage
   wb_stage

.. _if_stage:

Instruction Fetch (IF)
----------------------


Instruction Decode (ID)
-----------------------



Instruction Execute (EX)
------------------------



Memory Access (MEM)
-------------------



Write Back (WB)
---------------

