Instruction Decode (ID) Stage
=============================

The Instruction Decode (ID) stage executes in a single cycle and performs several key functions:

Control Signal Generation
-------------------------

Based on the fetched instruction, the ID stage generates the appropriate control signals for subsequent pipeline stages.  

Trap Generation
---------------

The ID stage can generate a trap in the following cases:  

- Illegal instructions  
- Machine-mode system calls (ECALL, EBREAK)  
- Other instruction-specific trap conditions  

Branch Prediction
-----------------

For branch instructions, the ID stage uses a branch predictor to predict the branch outcome and reduce stalls.  
- If the prediction is incorrect, the pipeline will be corrected in later stages.  

Immediate Generation
--------------------

The ID stage extracts the 32-bit immediate value from instructions when required, depending on the instruction type.  

Register File Access
--------------------

- Reads source register values required by the instruction.  
- If the Writeback (WB) stage is writing to a register that is being read in the ID stage, the value is **forwarded** to avoid stalls.  
