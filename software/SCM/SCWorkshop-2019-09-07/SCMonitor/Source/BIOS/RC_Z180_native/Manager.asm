; **********************************************************************
; **  Hardware Manager                          by Stephen C Cousins  **
; **  BIOS: RC_Z180_native                                            **
; **********************************************************************

; Bios constants - version number
#DEFINE     BNAME "Z180 native" ;Bios name
kBiosID:    .EQU BI_Z180N       ;Bios ID (use constant BI_xxxx)
kBiosMajor: .EQU 1              ;Bios version: major
kBiosMinor: .EQU 1              ;Bios version: minor
kBiosRevis: .EQU 0              ;Bios version: revision
;BiosTouch: .EQU 20190715       ;Last date this BIOS code touched


; **********************************************************************
; **  Includes                                                        **
; **********************************************************************

; Include jump table at start of BIOS
#INCLUDE    BIOS\BIOS_JumpTable.asm

; Include common BIOS functions and API shims
#INCLUDE    BIOS\BIOS_Common.asm

; Include any additional source files needed for this BIOS
#INCLUDE    BIOS\RC_Z180_native\Selftest.asm
#INCLUDE    BIOS\RC_Z180_native\Z180Support.asm


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
;   Console device 1 = Serial device at $C6 (Z180 port A)
;   Console device 2 = Serial device at $C7 (Z180 port B)
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
            LD   A,0x80         ;Bit 7 (Z180) set
            LD   (iHwFlags),A   ;Init hardware flags
            CALL Z180Init       ;Initialise Z180 CPU
; Set serial port A baud rate
            LD   A,(kaBaud1Def) ;Baud rate code, eg. 0x96 = 9600
            LD   C,1            ;Console device number (port A)
            CALL HW_SetBaud     ;Set baud rate
; Set serial port B baud rate
            LD   A,(kaBaud2Def) ;Baud rate code, eg. 0x96 = 9600
            LD   C,2            ;Console device number (port B)
            CALL HW_SetBaud     ;Set baud rate
; Install Z180's serial ports as console devices 1 and 2
            LD   HL,@PtrZ180    ;Pointer to vector list
            LD   B,4            ;Number of jump vectors
            LD   A,kFnDev1In    ;First device jump entry
            ;CALL InitJumps     ;Set up serial vectors
            JP   InitJumps      ;Set up serial vectors
; Jump table entries
@PtrZ180:   ; Device #4 = Z180's internal serial port 0
            .DW  Z180RxByteA
            .DW  Z180TxByteA
            ; Device #5 = Z180's internal serial port 1
            .DW  Z180RxByteB
            .DW  Z180TxByteB


; **********************************************************************
; H_GetName   see BIOS_Common.asm


; **********************************************************************
; H_GetVers   see BIOS_Common.asm


; **********************************************************************
; H_SetBaud   see Z180Support.asm


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

; H_PollT2 is in the Z180Support.asm


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








