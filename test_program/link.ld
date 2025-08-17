MEMORY
{
  IMEM (rx) : ORIGIN = 0x00000000, LENGTH = 0x00000400   /* 256 words × 32-bit = 1 KB */
  DMEM (rw) : ORIGIN = 0x00001000, LENGTH = 0x00000400   /* 256 words × 32-bit = 1 KB */
}

SECTIONS
{
  .text   : { *(.text*) } > IMEM
  .rodata : { *(.rodata*) } > DMEM   /* place read-only data in DMEM */
  .data   : { *(.data*) }   > DMEM
  .bss    : { *(.bss*) }    > DMEM
}

