; JC-BIOS MODEUP/RETMD trampoline (Z80)
;
; The ABI capsule pointer is loaded into HL before invoking the C emulation.
; Registers are preserved across the call per SPEC_MODE.

        .globl _jc_modeup_tramp
        .globl _jc_retmd_tramp
        .globl _jc_mode_capsule_ptr
        .globl _jc_modeup_emulate
        .globl _jc_retmd_emulate

_jc_modeup_tramp:
        di
        push af
        push bc
        push de
        push hl
        push ix
        push iy
        ex af, af'
        push af
        exx
        push bc
        push de
        push hl
        exx
        ex af, af'

        ld hl, (_jc_mode_capsule_ptr)
        call _jc_modeup_emulate

        ex af, af'
        exx
        pop hl
        pop de
        pop bc
        pop af
        exx
        ex af, af'

        pop iy
        pop ix
        pop hl
        pop de
        pop bc
        pop af
        ret

_jc_retmd_tramp:
        di
        push af
        push bc
        push de
        push hl
        push ix
        push iy
        ex af, af'
        push af
        exx
        push bc
        push de
        push hl
        exx
        ex af, af'

        call _jc_retmd_emulate

        ex af, af'
        exx
        pop hl
        pop de
        pop bc
        pop af
        exx
        ex af, af'

        pop iy
        pop ix
        pop hl
        pop de
        pop bc
        pop af
        ret
