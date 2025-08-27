;==================================================================================
; Grant Searle's code, modified for use with Small Computer Workshop IDE.
; Also the Compact Flash ready test has been improved and DRQ ready test added.
; Compatible with LiNC80 and RC2014 systems.
; SCC 2018-04-13
; Added option for 64MB compact flash.
; JL 2018-04-28
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

; To build Grant's original version uncomment this line
;#DEFINE    GrantsOriginal

; Set this definition (uncomment) to make a 64MB format utility
;#DEFINE    SIZE64

            .PROC Z80           ;SCWorkshop select processor
            .HEXBYTES 0x18      ;SCWorkshop Intel Hex output format


#IFDEF      SIZE64
numDrives   .EQU 7              ; Only 8 drives on 64MB card
#ELSE
numDrives   .EQU 15             ; Not including A:
#ENDIF

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

;====================================================================================

#IFDEF      GrantsOriginal
            .ORG 5000H          ; Format program origin.
#ELSE
            .ORG 0x8000
#ENDIF

            CALL printInline
            .TEXT "CP/M Formatter by G. Searle 2012"
            .DB CR,LF,0

            LD   A,'A'
            LD   (drvName),A

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


; There are 512 directory entries per disk, 4 DIR entries per sector
; So 128 x 128 byte sectors are to be initialised
; The drive uses 512 byte sectors, so 32 x 512 byte sectors per disk
; require initialisation

;Drive 0 (A:) is slightly different due to reserved track, so DIR sector starts at 32
            LD   A,(drvName)
            RST  08H            ; Print drive letter
            INC  A
            LD   (drvName),A
            LD   A,$20
            LD   (secNo),A

processSectorA:
            CALL cfWait

            LD   A,(secNo)
            OUT  (CF_LBA0),A
            LD   A,0
            OUT  (CF_LBA1),A
            LD   A,0
            OUT  (CF_LBA2),A
            LD   A,$E0
            OUT  (CF_LBA3),A
            LD   A,1
            OUT  (CF_SECCOUNT),A

            call writeDir

            LD   A,(secNo)
            INC  A
            LD   (secNo),A
            CP   $40
            JR   NZ, processSectorA


;Drive 1 onwards (B: etc) don't have reserved tracks, so sector starts at 0

            LD   DE,$0040       ; HL increment
            LD   HL,$0040       ; H = LBA2, L=LBA1, initialise for drive 1 (B:)
            LD   B,numDrives

processDirs:

            LD   A,(drvName)
            RST  08H            ; Print drive letter
            INC  A
            LD   (drvName),A

            LD   A,0
            LD   (secNo),A

processSector:
            CALL cfWait

            LD   A,(secNo)
            OUT  (CF_LBA0),A
            LD   A,L
            OUT  (CF_LBA1),A
            LD   A,H
            OUT  (CF_LBA2),A
            LD   A,0E0H
            OUT  (CF_LBA3),A
            LD   A,1
            OUT  (CF_SECCOUNT),A

            CALL writeDir

            LD   A,(secNo)
            INC  A
            LD   (secNo),A
            CP   $20
            JR   NZ, processSector

            ADD  HL,DE

            DEC  B
            JR   NZ,processDirs

            CALL printInline
            .DB CR,LF
            .TEXT "Formatting complete"
            .DB CR,LF,0

            RET

;================================================================================================
; Write physical sector to host
;================================================================================================

writeDir:
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
wr4secs:
            LD   HL,dirData
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

secNo       .DB  0
drvName     .DB  0


; Directory data for 1 x 128 byte sector
dirData:
            .DB $E5,$20,$20,$20,$20,$20,$20,$20,$20,$20,$20,$20,$00,$00,$00,$00
            .DB $00,$00,$00,$00,$00,$00,$00,$00,$00,$00,$00,$00,$00,$00,$00,$00

            .DB $E5,$20,$20,$20,$20,$20,$20,$20,$20,$20,$20,$20,$00,$00,$00,$00
            .DB $00,$00,$00,$00,$00,$00,$00,$00,$00,$00,$00,$00,$00,$00,$00,$00

            .DB $E5,$20,$20,$20,$20,$20,$20,$20,$20,$20,$20,$20,$00,$00,$00,$00
            .DB $00,$00,$00,$00,$00,$00,$00,$00,$00,$00,$00,$00,$00,$00,$00,$00

            .DB $E5,$20,$20,$20,$20,$20,$20,$20,$20,$20,$20,$20,$00,$00,$00,$00
            .DB $00,$00,$00,$00,$00,$00,$00,$00,$00,$00,$00,$00,$00,$00,$00,$00

            .END
            







