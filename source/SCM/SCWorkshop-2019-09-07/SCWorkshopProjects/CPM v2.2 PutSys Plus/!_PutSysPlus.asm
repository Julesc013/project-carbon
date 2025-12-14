;==================================================================================
; Grant Searle's code, modified for use with Small Computer Workshop IDE.
; Also embedded CP/M hex files into this utility to make it easier to use.
; Compile options for LiNC80 and RC2014 systems.
; SCC 2018-04-13
;
; SCC  2019-03-08 : Added support for Z80sc
; SCC  2019-05-04 : Added support for Z180 (eg. SC111+SC119)
; SCC  2019-05-27 : Added support for Z50Bus (eg. SC118+SC125)
; SCC  2019-06-27 : Added support for SC126 Z180 motherboard
;
;==================================================================================
; Contents of this file are copyright Grant Searle
;
; You have permission to use this for NON COMMERCIAL USE ONLY
; If you wish to use it elsewhere, please include an acknowledgement to myself.
;
; http://searle.hostei.com/grant/index.html
;
; eMail: home.micros01@btinternet.com
;
; If the above don't work, please perform an Internet search to see if I have
; updated the web page hosting service.
;
;==================================================================================

; NOTE: Some memory locations are overwritten when HEX files are inserted

            .PROC Z80           ;SCWorkshop select processor
            .HEXBYTES 0x18      ;SCWorkshop Intel Hex output format

; Define one of these to select which build is required
;#DEFINE    GrantsOriginal
;#DEFINE    LiNC80_SIO_CF64
;#DEFINE    LiNC80_SIO_CF128
;#DEFINE    RC2014_SIO_CF64
;#DEFINE    RC2014_SIO_CF128
;#DEFINE    RC2014_ACIA_CF64
;#DEFINE    RC2014_ACIA_CF128
;#DEFINE    Z80sc_SIO_CF64
;#DEFINE    Z80sc_SIO_CF128
;#DEFINE    Z180_SCM_S5_CF128
;#DEFINE    Z50Bus_SIO_CF128
;#DEFINE    RC_Z180_Native_CF128
#DEFINE     SC126_CF128

;==================================================================================

#IFDEF      GrantsOriginal
CodeORG     .EQU 05000H         ;Code runs here
loadAddr    .EQU 0D000H         ;CP/M hex files load here
#ELSE
CodeORG     .EQU 08000H         ;Code runs here
loadAddr    .EQU 09000H         ;CP/M hex files load here
#ENDIF
numSecs     .EQU 24             ;Number of 512 sectors to be loaded


; CF registers
CF_DATA     .EQU $10
CF_FEATURES .EQU $11
CF_ERROR    .EQU $11
CF_SECCOUNT .EQU $12
CF_SECTOR   .EQU $13
CF_CYL_LOW  .EQU $14
CF_CYL_HI   .EQU $15
CF_HEAD     .EQU $16
CF_STATUS   .EQU $17
CF_COMMAND  .EQU $17
CF_LBA0     .EQU $13
CF_LBA1     .EQU $14
CF_LBA2     .EQU $15
CF_LBA3     .EQU $16

;CF Features
CF_8BIT     .EQU 1
CF_NOCACHE  .EQU 082H
;CF Commands
CF_READ_SEC .EQU 020H
CF_WRITE_SEC                    .EQU 030H
CF_SET_FEAT .EQU 0EFH

LF          .EQU 0AH            ;line feed
FF          .EQU 0CH            ;form feed
CR          .EQU 0DH            ;carriage RETurn

;================================================================================================

            .ORG CodeORG        ;Code runs here

            CALL printInline
            .TEXT "CP/M System Transfer by G. Searle 2012"
            .DB  CR,LF,0

            CALL cfWait
            LD   A,CF_8BIT      ; Set IDE to be 8bit
            OUT  (CF_FEATURES),A
            LD   A,CF_SET_FEAT
            OUT  (CF_COMMAND),A

            CALL cfWait
            LD   A,CF_NOCACHE   ; No write cache
            OUT  (CF_FEATURES),A
            LD   A,CF_SET_FEAT
            OUT  (CF_COMMAND),A

            LD   B,numSecs

            LD   A,0
            LD   (secNo),A
            LD   HL,loadAddr
            LD   (dmaAddr),HL
processSectors:

            CALL cfWait

            LD   A,(secNo)
            OUT  (CF_LBA0),A
            LD   A,0
            OUT  (CF_LBA1),A
            OUT  (CF_LBA2),A
            LD   A,0E0H
            OUT  (CF_LBA3),A
            LD   A,1
            OUT  (CF_SECCOUNT),A

            CALL write

            LD   DE,0200H
            LD   HL,(dmaAddr)
            ADD  HL,DE
            LD   (dmaAddr),HL
            LD   A,(secNo)
            INC  A
            LD   (secNo),A

#IFNDEF     GrantsOriginal
            LD A,'.'
            RST 08
#ENDIF

            DJNZ processSectors

            CALL printInline
            .DB  CR,LF
            .TEXT "System transfer complete"
            .DB  CR,LF,0

            RET


;================================================================================================
; Write physical sector to host
;================================================================================================

write:
            PUSH AF
            PUSH BC
            PUSH HL

            CALL cfWait

            LD   A,CF_WRITE_SEC
            OUT  (CF_COMMAND),A

            CALL cfWait

#IFNDEF     GrantsOriginal
@TstDRQ:    IN   A,(CF_STATUS)  ;Read status register
            BIT  3,A            ;Test DRQ flag
            JR   Z,@TstDRQ      ;Low so not ready
#ENDIF

            LD   C,4
            LD   HL,(dmaAddr)
wr4secs:
            LD   B,128
wrByte:     LD   A,(HL)
            NOP
            NOP
            OUT  (CF_DATA),A
            INC  HL
            DEC  B
            JR   NZ, wrByte

            DEC  C
            JR   NZ,wr4secs

            POP  HL
            POP  BC
            POP  AF

            RET

;================================================================================================
; Wait for disk to be ready (busy=0,ready=1)
;================================================================================================

#IFDEF      GrantsOriginal
cfWait:     PUSH AF
cfWait1:    IN   A,(CF_STATUS)
            AND  080H
            CP   080H
            JR   Z,cfWait1
            POP  AF
            RET
#ELSE
cfWait:     PUSH AF
@TstBusy:   IN   A,(CF_STATUS)  ;Read status register
            BIT  7,A            ;Test Busy flag
            JR   NZ,@TstBusy    ;High so busy
@TstReady:  IN   A,(CF_STATUS)  ;Read status register
            BIT  6,A            ;Test Ready flag
            JR   Z,@TstBusy     ;Low so not ready
            POP  AF
            RET
#ENDIF

;================================================================================================
; Utilities
;================================================================================================

printInline:
            EX   (SP),HL        ; PUSH HL and put RET ADDress into HL
            PUSH AF
            PUSH BC
nextILChar: LD   A,(HL)
            CP   0
            JR   Z,endOfPrint
            RST  08H
            INC  HL
            JR   nextILChar
endOfPrint: INC  HL             ; Get past "null" terminator
            POP  BC
            POP  AF
            EX   (SP),HL        ; PUSH new RET ADDress on stack and restore HL
            RET

dmaAddr     .DW  0
secNo       .DB  0

;================================================================================================
; CP/M system files to be copied to Compact Flash
;================================================================================================

#IFNDEF     GrantsOriginal

kAddrCPM:   .EQU loadAddr       ;CP/M v2.2 load address, executes at 0xD000
kAddrBIOS:  .EQU loadAddr+0x1600  ; CP/M BIOS load address, executes at 0xE600

            .ORG kAddrCPM

; CP/M v2.2 BDOS common to all platforms
#INSERTHEX  Includes/BDOS_22.HEX

            .ORG kAddrBIOS

; LiNC80 BIOS
#IFDEF      LiNC80_SIO_CF64
#INSERTHEX  Includes/CBIOS_LiNC80_SIO_CF64.HEX 
#ENDIF
#IFDEF      LiNC80_SIO_CF128
#INSERTHEX  Includes/CBIOS_LiNC80_SIO_CF128.HEX 
#ENDIF

; RC2014 BIOS (SIO version slightly modified from standard distribution)
#IFDEF      RC2014_ACIA_CF64
#INSERTHEX  Includes/CBIOS_RC2014_ACIA_CF64.HEX 
#ENDIF
#IFDEF      RC2014_ACIA_CF128
#INSERTHEX  Includes/CBIOS_RC2014_ACIA_CF128.HEX 
#ENDIF
#IFDEF      RC2014_SIO_CF64
#INSERTHEX  Includes/CBIOS_RC2014_SIO_CF64.HEX 
#ENDIF
#IFDEF      RC2014_SIO_CF128
#INSERTHEX  Includes/CBIOS_RC2014_SIO_CF128.HEX 
#ENDIF

; Z80sc BIOS
#IFDEF      Z80sc_SIO_CF64
#INSERTHEX  Includes/CBIOS_Z80sc_SIO_CF64.HEX 
#ENDIF
#IFDEF      Z80sc_SIO_CF128
#INSERTHEX  Includes/CBIOS_Z80sc_SIO_CF128.HEX 
#ENDIF

; Z180 BIOS
#IFDEF      Z180_SCM_S5_CF128
#INSERTHEX  Includes/CBIOS_Z180_SCM_S5_CF128.HEX 
;#INSERTHEX Includes/IntelHex.hex 
#ENDIF

#IFDEF      Z50Bus_SIO_CF128
#INSERTHEX  Includes/CBIOS_Z50Bus_SIO_CF128.HEX 
#ENDIF

#IFDEF      RC_Z180_Native_CF128
#INSERTHEX  Includes/CBIOS_RC-Z180-Native_CF128.HEX 
#ENDIF


#IFDEF      SC126_CF128
#INSERTHEX  ../CPM v2.2 CBIOS/SC126_CBIOS_CF128.HEX 
#ENDIF


#ENDIF
            .END

















