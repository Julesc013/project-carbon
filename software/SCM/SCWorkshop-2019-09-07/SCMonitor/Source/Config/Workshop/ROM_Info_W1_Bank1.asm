; **********************************************************************
; **  ROM info: 08kBanks-Bank1-Standard         by Stephen C Cousins  **
; **********************************************************************

            .CODE

; Help extension: BASIC.HLP
BasicHelp:  .DB  "BASIC    Grant Searle's adaptation of Microsoft BASIC",0x0D,0x0A
            .DB  "WBASIC   Warm start BASIC (retains BASIC program)",0x0D,0x0A
            .DB  0
BasicHelpEnd:

            .ORG 0x3FE0

            .DW  0xAA55         ;Identifier
            .DB  "BASIC   "     ;File name ("BASIC.HLP")
            .DB  0x03           ;File type 3 = Help
            .DB  0              ;Not used
            .DW  BasicHelp      ;Start address
            .DW  BasicHelpEnd-BasicHelp ;Length




#DEFINE     Monitor/IncludeMonitorInfo
; Include Monitor.EXE information at top of bank 1. eg:
;           .ORG 0x1FF0         ;First ROMFS file in 8k bank
;           .DW  0xAA55         ;Identifier
;           .DB  "Monitor "     ;File name ("Monitor.EXE")
;           .DB  2              ;File type 2 = Executable from ROM
;           .DB  0              ;Not used
;           .DW  0x0000         ;Start address
;           .DW  0x2000         ;Length

; **********************************************************************
; **  End of ROM information module                                   **
; **********************************************************************





