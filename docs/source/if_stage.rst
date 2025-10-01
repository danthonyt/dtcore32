Instruction Fetch (IF) Stage
============================

The Instruction Fetch (IF) stage communicates with the instruction memory interface 
to retrieve instructions. It operates over two cycles:  

1. In the first cycle, the instruction address is sent to the instruction memory (IMEM).  
2. In the second cycle, the instruction output is read from IMEM.  

These operations are pipelined, so under normal conditions the IF stage fetches one instruction per cycle.  
The fetched instruction, along with its address, is then passed to the Instruction Decode (ID) stage.  

Certain events can disrupt this flow, causing the IF stage to stall and take two full cycles 
instead of completing one fetch per cycle. These are listed below in order of priority:

Committed Trap Instruction
--------------------------

When a trapped instruction is committed in the Writeback stage, the program counter (PC) 
of the IF stage jumps to the trap handler address, specified in the `MTVEC` CSR.  

- `MCAUSE` holds the cause of the trapped instruction.  
- `MEPC` stores the address of the trapped instruction.  

Mispredicted Branch
-------------------

The Instruction Decode (ID) stage uses a branch predictor to reduce stalls caused by branches.  
The actual branch result is resolved in the Execute (EX) stage and passed to the Memory (MEM) stage, 
where it becomes visible to the IF stage.  

If the predicted branch result does not match the actual outcome:  

- The pipeline is flushed.  
- The PC is updated to the correct branch target address.  

Predicted Branch
----------------

If the Instruction Decode (ID) stage predicts that a branch will be taken:  

- The IF stage is flushed.  
- The PC is updated to the predicted branch target.  

Normal Operation
----------------

In the absence of traps or branches, the IF stage increments the PC and fetches the next sequential instruction.
