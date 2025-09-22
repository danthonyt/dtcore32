ENTRY(_start)

MEMORY
{
  IMEM (rx)  : ORIGIN = 0x00000000, LENGTH = 64K   /* instruction + read-only memory */
  DMEM (rwx) : ORIGIN = 0x00100000, LENGTH = 64K   /* data memory */
}

SECTIONS
{
  /* Code (instructions only) in IMEM */
  .text : {
    *(.text)       /* program code */
    *(.text*)      
  } > IMEM

  /* Read-only data in IMEM (now moved from DMEM) */
  .rodata : {
    *(.rodata)
    *(.rodata*)
  } > IMEM

  /* Initialized data in DMEM */
  .data : {
    *(.data)
    *(.data*)
  } > DMEM

  /* Uninitialized data in DMEM */
  .bss : {
    __bss_start = .;
    *(.bss)
    *(.bss*)
    *(COMMON)
    __bss_end = .;
  } > DMEM

  /* Heap region */
  .heap (NOLOAD) : {
    _heap_start = .;
  } > DMEM

  /* Stack region at top of DMEM */
  .stack (NOLOAD) : {
    _stack_end = ORIGIN(DMEM) + LENGTH(DMEM);
    _stack_start = _stack_end - 8K; /* reserve 8KB for stack */
  } > DMEM
}
