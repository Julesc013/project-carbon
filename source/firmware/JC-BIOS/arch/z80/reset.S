; JC-BIOS reset trampoline (Z80)
;
; Responsibilities:
; - Mask interrupts
; - Establish stack pointer
; - Jump to bios C entry

        .globl _jc_reset
        .globl _jc_bios_p0_entry
        .globl _jc_bsp_stack_top

_jc_reset:
        di
        ld sp, (_jc_bsp_stack_top)
        jp _jc_bios_p0_entry
