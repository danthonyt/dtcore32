
/* Specify the memory areas */
MEMORY
{
ROM (rx)      : ORIGIN =  0x00000000, LENGTH = 64K
RAM (xrw)      : ORIGIN = 0x00100000, LENGTH = 64K
}
/* Define output sections */
SECTIONS
{
  /* The program code and other data goes into ROM */
  .text :
  {
    *(.text)           /* .text sections (code) */
    *(.text*)          /* .text* sections (code) */
    . = ALIGN(4);
    _etext = .;        /* define a global symbols at end of code */
  } >ROM

/* Constant data goes into ROM */
  .rodata :
  {
    *(.rodata)         /* .rodata sections (constants, strings, etc.) */
    *(.rodata*)        /* .rodata* sections (constants, strings, etc.) */
    . = ALIGN(4);
  } >ROM
  

.data : {
    _sdata = .;
    *(.data)
    *(.data*)
    . = ALIGN(4);
    _edata = .;
} >RAM AT>ROM

.sdata : {
    _ssdata = .;
    *(.sdata)
    *(.sdata*)
    . = ALIGN(4);
    _esdata = .;
} >RAM AT>ROM

/* Let the linker give us the actual ROM addresses */
_sidata   = LOADADDR(.data);    /* points to ROM copy of .data */
_sisddata = LOADADDR(.sdata);   /* points to ROM copy of .sdata */


  
  /* Uninitialized data section */
  . = ALIGN(4);
  .bss :
  {
    /* This is used by the startup in order to initialize the .bss section */
    _sbss = .;         /* define a global symbol at bss start */
    *(.bss)
    *(.bss*)
    *(COMMON)
    . = ALIGN(32);
    _ebss = .;         /* define a global symbol at bss end */
  } >RAM

  /* Stack at top of RAM */
    .stack (NOLOAD) : ALIGN(8)
    {
        _stack_end   = ORIGIN(RAM) + LENGTH(RAM);
        _stack_start = _stack_end - 0x2000; /* 8KB stack */
    } >RAM
}