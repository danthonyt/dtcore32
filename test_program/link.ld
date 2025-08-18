MEMORY
{
  IMEM (rx)  : ORIGIN = 0x00000000, LENGTH = 0x00000400
  DMEM (rw)  : ORIGIN = 0x00001000, LENGTH = 0x00000400
}

SECTIONS
{
  .text   : { *(.text*) } > IMEM
  .rodata : { *(.rodata*) } > DMEM
  .data   : { *(.data*) }   > DMEM
  .bss    : { *(.bss*) }    > DMEM
}

/* define stack symbols at very end of DMEM */
_stack_top    = 0x13F0;
_stack_bottom = 0x1200;
