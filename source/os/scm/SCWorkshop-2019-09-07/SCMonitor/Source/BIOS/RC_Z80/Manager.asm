; **********************************************************************
; **  Hardware Manager                          by Stephen C Cousins  **
; **  BIOS: RC_Z80                                                    **
; **********************************************************************

; Bios constants - version number
#DEFINE     BNAME "RC-Z80"      ;Bios name
kBiosID:    .EQU BI_SC114       ;Bios ID (use constant BI_xxxx)
kBiosMajor: .EQU 1              ;Bios version: major
kBiosMinor: .EQU 1              ;Bios version: minor
kBiosRevis: .EQU 0              ;Bios version: revision
;BiosTouch: .EQU 20190906       ;Last date this BIOS code touched


; Global constants - motherboard hardware
kPrtLED:    .EQU 0x08           ;Motherboard LED port (active low)
kRtsPrt:    .EQU 0x20           ;/RTS output is bit zero
kTxPrt:     .EQU 0x28           ;Transmit output is bit zero
kRxPrt:     .EQU 0x28           ;Receive input is bit 7
kBankPrt:   .EQU 0x30           ;Motherboard bank select port 




; **********************************************************************
; **  Includes                                                        **
; **********************************************************************

; Include jump table at start of BIOS
#INCLUDE    BIOS\BIOS_JumpTable.asm

; Include common BIOS functions and API shims
#INCLUDE    BIOS\BIOS_Common.asm

; Include any additional source files needed for this BIOS
#INCLUDE    BIOS\RC_Z80\Selftest.asm
#INCLUDE    BIOS\RC_Z80\Serial_SCS2_BitBang.asm
;#INCLUDE   BIOS\RC_Z180_native\Z180Support.asm


; **********************************************************************
; Ensure we assemble to code area

            .CODE

; **********************************************************************
; Self-test
;   On entry: No parameters required
;   On exit:  AF BC DE HL not specified
;             IX IY I AF' BC' DE' HL' not specified
; H_Test      see Selftest.asm


; **********************************************************************
; Initialise BIOS and hardware
;   On entry: No parameters required
;   On exit:  AF BC DE HL not specified
;             IX IY I AF' BC' DE' HL' preserved
; Identify and initialise console devices:
;   Console device 1 = Serial Z80 SIO port A
;                   or Serial ACIA number 1
;   Console device 2 = Serial Z80 SIO port B
;   Console device 3 = Serial ACIA number 2
;   Console device 6 = Serial bit-bang port
; Sets up hardware present flags:
;   Bit 0 = ACIA #1 
;   Bit 1 = SIO #1
;   Bit 2 = ACIA #2
;   Bit 3 = Bit-bang serial
;   Bit 4 = CTC #1
;   Bit 5 = SIO #2 
;   Bit 6 = CTC #2
;   Bit 7 = Z180 serial
H_Init:     ;CALL RomInitialise ;Initialise ROM filing system
            LD   A,0x08         ;Bit 3 set (bit-bang serial)
            LD   (iHwFlags),A   ;Init hardware flags
            ;CALL Z180Init      ;Initialise Z180 CPU
; Initialise SC_S2 bit-bang serial port as device 6
            CALL SCS2_bbInit    ;Initialise bit-bang serial
            LD   HL,@PtrBB      ;Pointer to vector list
            LD   B,2            ;Number of jump vectors
            LD   A,kFnDev1In    ;First device jump entry
            CALL InitJumps      ;Set up serial vectors

            RET

; Set serial port A baud rate
            LD   A,(kaBaud1Def) ;Baud rate code, eg. 0x96 = 9600
            LD   C,1            ;Console device number (port A)
            ;CALL HW_SetBaud    ;Set baud rate
; Set serial port B baud rate
            LD   A,(kaBaud2Def) ;Baud rate code, eg. 0x96 = 9600
            LD   C,2            ;Console device number (port B)
            ;CALL HW_SetBaud    ;Set baud rate
; Install Z180's serial ports as console devices 1 and 2
            ;LD   HL,@PtrZ180   ;Pointer to vector list
            ;LD   B,4           ;Number of jump vectors
            ;LD   A,kFnDev1In   ;First device jump entry
            ;CALL InitJumps     ;Set up serial vectors
            ;JP   InitJumps     ;Set up serial vectors
; Jump table entries
@PtrBBx:    ; Device #4 = Z180's internal serial port 0
            ;.DW  Z180RxByteA
            ;.DW  Z180TxByteA
            ; Device #5 = Z180's internal serial port 1
            ;.DW  Z180RxByteB
            ;.DW  Z180TxByteB
@PtrBB:     ; Device #6 = Serial bit-bang SC114
            .DW  SCS2_bbRx
            .DW  SCS2_bbTx


; **********************************************************************
; H_GetName   see BIOS_Common.asm


; **********************************************************************
; H_GetVers   see BIOS_Common.asm


; **********************************************************************
; H_SetBaud   see Z180Support.asm
H_SetBaud:  RET


; **********************************************************************
; Idle event set up
;   On entry: A = Idle event configuration:
;                 0 = Off (just execute RET instruction)
;                 1 = Software generated timer events
;                 2 = Hardware generated timer events
;   On exit:  AF BC DE HL not specified
;             IX IY I AF' BC' DE' HL' preserved
H_IdleSet:  LD   HL,@Vector     ;Point to idle mode 0 vector
            OR   A              ;A=0?
            JR   Z,@IdleSet     ;Yes, so skip
            INC  HL             ;Point to idle mode 1 vector
            INC  HL
; Set up event handler by writing to jump table
@IdleSet:   LD   A,kFnIdle      ;Jump table 0x0C = idle handler
            JP   InitJump       ;Write jump table entry A
; Idle events off handler 
@Return:    XOR  A              ;Return no event (A=0 and Z flagged)
            RET                 ;Idle mode zero routine
; Vector for event handler
@Vector:    .DW  @Return        ;Mode 0 = Off
            .DW  H_PollT2       ;Mode 1 = Hardware, no software version

H_PollT2:   RET


; **********************************************************************
; Output devices message
;   On entry: No parameters required
;   On exit:  AF BC DE HL not specified
;             IX IY I AF' BC' DE' HL' preserved
H_MsgDevs:  LD   DE,@szHwZ180   ;Serial Z180 message
            JP   OutputStr      ;Yes, so list it

@kChar:     .EQU kZ180Base / 16 ;Z180 base address high nibble

@szHwZ180:  .DB  "1 = Z180 port A    (@",HEXCHAR @kChar,"6)",kNewLine
            .DB  "2 = Z180 port B    (@",HEXCHAR @kChar,"7)",kNewLine
            .DB  kNull


; **********************************************************************
; Read from banked RAM
;   On entry: DE = Address in secondary bank
;   On exit:  A = Byte read from RAM
;             F BC DE HL not specified
;             IX IY I AF' BC' DE' HL' preserved
H_RdRAM:    RET                 ;Banked RAM not supported


; **********************************************************************
; Write to banked RAM
;   On entry: A = Byte to be written to RAM
;             DE = Address in secondary bank
;   On exit:  AF BC DE HL not specified
;             IX IY I AF' BC' DE' HL' preserved
H_WrRAM:    RET                 ;Banked RAM not supported


; **********************************************************************
; Copy from banked ROM to RAM
;   On entry: A = ROM bank number (0 to n)
;             HL = Source start address (in ROM)
;             DE = Destination start address (in RAM)
;             BC = Number of bytes to copy
;   On exit:  AF BC DE HL not specified
;             IX IY I AF' BC' DE' HL' preserved
H_CopyROM:  LDIR                ;Only one bank so just copy memory
            RET


; **********************************************************************
; Execute code in ROM bank
;   On entry: A = ROM bank number (0 to 3)
;             DE = Absolute address to execute
;   On exit:  AF BC DE HL not specified
;             IX IY I AF' BC' DE' HL' preserved
H_ExecROM:  PUSH DE             ;Jump to DE by pushing on
            RET                 ;  to stack and 'returning'


; **********************************************************************
; H_Delay     see BIOS_Common.asm


; **********************************************************************
; **  Public workspace (in RAM)                                       **
; **********************************************************************

            .DATA




