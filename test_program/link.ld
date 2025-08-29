MEMORY
{
  IMEM (rx)  : ORIGIN = 0x00000000,  LENGTH = 0x000003FF
  DMEM (rw)  : ORIGIN = 0x00100000, LENGTH = 0x000003FF
}


SECTIONS
{
  .text   : { *(.text*) } > IMEM
  .rodata : { *(.rodata*) } > DMEM
  .data : {
    _sdata = .;
    *(.data*)
    _edata = .;
} > DMEM AT> IMEM
  .bss : {
    _sbss = .;
    *(.bss*)
    *(COMMON)
    _ebss = .;
} > DMEM

}

/* define stack symbols at very end of DMEM */
_stack_top    = 0x0010003FE;
_stack_bottom = 0x0010002FF;



