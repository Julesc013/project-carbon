; **********************************************************************
; **  Config: Standard features                 by Stephen C Cousins  **
; **********************************************************************

; **********************************************************************
; Hardware identifier constants 
;
; These provide the ID for a specific hardware design. They are used in
; the BUILD.ASM file statement:  kConfHardw:  .SET HW_xxxx
; If the configuration is to be used with more than one hardware design, 
; use the value HW_UNKNOWN.
;
; Symbol     Value              Description
; ======     =====              ===========
HW_UNKNOWN: .EQU 0              ;Unknown or Custom hardware
HW_WSHOP:   .EQU 1              ;SC Workshop / simulated 
HW_SCDEV:   .EQU 2              ;SC Development Kit 01
HW_RC2014:  .EQU 3              ;RC2014 Generic 
HW_SBC1:    .EQU 5              ;LiNC80 SBC1 with Z50Bus
HW_TomSBC:  .EQU 6              ;Tom Szolyga's Z80 SBC rev C
HW_Z280RC:  .EQU 7              ;Bill Shen's Z280RC
HW_Z80SBC:  .EQU 9              ;Bill Shen's Z80SBC RC
HW_SC101:   .EQU 101            ;SC101 Prototype motherboard
HW_SC108:   .EQU 108            ;SC126 Z80 processor for RC2014
HW_SC111:   .EQU 111            ;SC111 Z180 processor for RC2014+
HW_SC114:   .EQU 114            ;SC114 Z80 SBC / motherboard for
HW_SC118:   .EQU 118            ;SC118 Z80 processor for Z50Bus
HW_SC121:   .EQU 121            ;SC121 Z80 processor for Z50sc
HW_SC126:   .EQU 126            ;SC126 Z180 SBC / motherboard


; **********************************************************************
; Default configuration details

; Configuration identifiers
kConfMajor: .EQU '0'            ;Config: Letter = official, number = user
kConfMinor: .EQU '0'            ;Config: 1 to 9 = official, 0 = user
;#DEFINE    CNAME "Simulated"   ;Configuration name (max 11 characters)

; Hardware ID (use HW_UNKNOWN if not for a very specified product)
kConfHardw: .EQU HW_UNKNOWN     ;Hardware identifier (if known)

; Console devices
kConDef:    .EQU 1              ;Default console device (1 to 6)
kBaud1Def:  .EQU 0x11           ;Console device 1 default baud rate 
kBaud2Def:  .EQU 0x11           ;Console device 2 default baud rate 

; Simple I/O ports
kPrtIn:     .EQU 0x00           ;General input port
kPrtOut:    .EQU 0x00           ;General output port

; ROM filing system
kROMBanks:  .EQU 1              ;Number of software selectable ROM banks
kROMTop:    .EQU 0x7F           ;Top of banked ROM (hi byte only)

; Processor
;#DEFINE    PROCESSOR Z180      ;Processor type "Z80", "Z180"
kCPUClock:  .EQU 18432000       ;CPU clock speed in Hz
kZ180Base:  .EQU 0xC0           ;Z180 internal register base address


; Memory map (code)
kCode:      .EQU 0x0000         ;Typically 0x0000 or 0xE000

; Memory map (data in RAM)
kData:      .EQU 0xFC00         ;Typically 0xFC00 (to 0xFFFF)


; **********************************************************************
; Optional features (comment out or rename unwanted features)
; Excluding any of these may result in bugs as I don't test every option
; Exporting functions:
#DEFINE     IncludeAPI          ;Application Programming Interface (API)
#DEFINE     IncludeFDOS         ;Very limited CP/M style FDOS support
; Support functions:
#DEFINE     IncludeStrings      ;String support (needs utilities)
#DEFINE     IncludeUtilities    ;Utility functions (needs strings)
; Monitor functions:
#DEFINE     IncludeMonitor      ;Monitor essentials
#DEFINE     IncludeAssembler    ;Assembler (needs disassembler)
#DEFINE     IncludeBaud         ;Baud rate setting
#DEFINE     IncludeBreakpoint   ;Breakpoint and single stepping
#DEFINE     IncludeCommands     ;Command Line Interprester (CLI)
#DEFINE     IncludeDisassemble  ;Disassembler 
#DEFINE     IncludeHelp         ;Extended help text
#DEFINE     IncludeHexLoader    ;Intel hex loader
#DEFINE     IncludeMiniTerm     ;Mini terminal support
;#DEFINE    IncludeTrace        ;Trace execution
; Extensions:
#DEFINE     IncludeRomFS        ;ROM filing system
;#DEFINE    IncludeScripting    ;Simple scripting (needs monitor)
#DEFINE     IncludeSelftest     ;Self test at reset


; **********************************************************************
; **  End of standard configuration details                           **
; **********************************************************************












