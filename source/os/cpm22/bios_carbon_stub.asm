; Carbon CP/M 2.2 BIOS stub (Z80/8080-compatible subset)
; This is a minimal shim for console I/O and BSP discovery.
; Disk routines are TODO in this stub and currently return error.

            org     0E000h

jmp_boot:   jmp     boot
jmp_wboot:  jmp     wboot
jmp_const:  jmp     const
jmp_conin:  jmp     conin
jmp_conout: jmp     conout
jmp_list:   jmp     list
jmp_punch:  jmp     punch
jmp_reader: jmp     reader
jmp_home:   jmp     home
jmp_seldsk: jmp     seldsk
jmp_settrk: jmp     settrk
jmp_setsec: jmp     setsec
jmp_setdma: jmp     setdma
jmp_read:   jmp     read
jmp_write:  jmp     write
jmp_listst: jmp     listst
jmp_sectran:jmp     sectran

boot:
            call    bios_init
            lxi     sp, 0FFFFh
            lxi     h, 0080h
            shld    dma_addr
            jmp     wboot

wboot:
            jmp     0100h

const:
            ; TODO: patch console status port from BSP.
            in      00h
            ani     01h
            jz      const_none
            mvi     a, 0FFh
            ret
const_none:
            xra     a
            ret

conin:
conin_wait:
            call    const
            ora     a
            jz      conin_wait
            ; TODO: patch console data port from BSP.
            in      00h
            ret

conout:
            mov     a, c
            ; TODO: patch console data port from BSP.
            out     00h
            ret

list:
            jmp     conout

punch:
            jmp     conout

reader:
            jmp     conin

home:
            lxi     h, 0000h
            shld    track
            ret

seldsk:
            mov     a, c
            sta     drive
            ora     a
            jz      seldsk_ok
            lxi     h, 0000h
            ret
seldsk_ok:
            lxi     h, dph0
            ret

settrk:
            mov     h, b
            mov     l, c
            shld    track
            ret

setsec:
            mov     a, c
            sta     sector
            ret

setdma:
            mov     h, b
            mov     l, c
            shld    dma_addr
            ret

read:
            mvi     a, 01h
            ret

write:
            mvi     a, 01h
            ret

listst:
            mvi     a, 0FFh
            ret

sectran:
            mov     h, b
            mov     l, c
            ret

bios_init:
            ; TODO: read BSP at 0FF00h and patch console/disk ports.
            ret

; --------------------------------------------------------------------------
; BIOS data
; --------------------------------------------------------------------------
track:      dw      0000h
sector:     db      00h
drive:      db      00h
dma_addr:   dw      0080h

dph0:       dw      0000h
            dw      0000h
            dw      0000h
            dw      0000h
            dw      dirbuf
            dw      dpb
            dw      0000h
            dw      0000h

dirbuf:     ds      128
dpb:        ds      15
