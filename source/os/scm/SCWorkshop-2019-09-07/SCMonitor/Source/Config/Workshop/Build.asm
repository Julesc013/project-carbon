; **********************************************************************
; **  Build Small Computer Monitor Configuration W1 (SCWorkshop)      **
; **********************************************************************

#TARGET     Simulated_Z80       ;Determines hardware support included

; Build date
#DEFINE     CDATE "20190711"    ;Build date is embedded in the code

; Configuration identifiers
kConfMajor: .SET 'W'            ;Config: Letter = official, number = user
kConfMinor: .SET '1'            ;Config: 1 to 9 = official, 0 = user
#DEFINE     CNAME "Simulated"   ;Configuration name (max 11 characters)

; Hardware ID (use HW_UNKNOWN if not for a very specified product)
kConfHardw: .SET HW_WSHOP       ;Hardware identifier (if known)

; Console devices
kConDef:    .SET 1              ;Default console device (1 to 6)
kBaud1Def:  .SET 0x11           ;Console device 1 default baud rate 
kBaud2Def:  .SET 0x11           ;Console device 2 default baud rate 

; Simple I/O ports
kPrtIn:     .SET 0x00           ;General input port
kPrtOut:    .SET 0x00           ;General output port

; ROM filing system
kROMBanks:  .SET 1              ;Number of software selectable ROM banks
kROMTop:    .SET 0x7F           ;Top of banked ROM (hi byte only)

; Processor
#DEFINE     PROCESSOR Z80       ;Processor type "Z80", "Z180"
kCPUClock:  .SET 4000000        ;CPU clock speed in Hz
;kZ180Base: .SET 0xC0           ;Z180 internal register base address


; **********************************************************************
; Build the code

#INCLUDE    System\Begin.asm

#INCLUDE    BIOS\Workshop\Manager.asm

#INCLUDE    System\End.asm

#INCLUDE    Config\Workshop\ROM_Info.asm













