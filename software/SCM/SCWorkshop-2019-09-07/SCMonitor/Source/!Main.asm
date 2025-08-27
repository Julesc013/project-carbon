; **********************************************************************
; **  Small Computer Monitor (SCMonitor)        by Stephen C Cousins  **
; **                                                                  **
; **  Developed with Small Computer Workshop (IDE)     www.scc.me.uk  **
; **********************************************************************

; **********************************************************************
; Only one build can be defined so comment out the others
; 1st character (major identifier): letter=official, number=user/custom
; 2nd character (minor identifier): 1-9=official, 0=user/custom
;
;#DEFINE    BUILD 00            ;Complete custom/user build

;#DEFINE    BUILD C1            ;Z80sc  standard ROM

;#DEFINE    BUILD F1            ;SC_F1  Z50Bus standard ROM

;#DEFINE    BUILD L1            ;LiNC80 SBC1 standard 32k ROM

;#DEFINE    BUILD Q9            ;SC_S6  Z180 (eg. SC126)

;#DEFINE    BUILD R1            ;RC2014 08K ROM 32K RAM standard
;#DEFINE    BUILD R2            ;RC2014 16K ROM 48K RAM standard
;#DEFINE    BUILD R3            ;RC2014 32K ROM 32/64K RAM paged
;#DEFINE    BUILD R4            ;RC2014 16K ROM 32/64K RAM paged

;#DEFINE    BUILD S1            ;SC_S1  SC101 standard ROM
;#DEFINE    BUILD S2            ;SC_S2  SC114 standard ROM
;#DEFINE    BUILD S3            ;SC_S3  SC108 standard ROM
;#DEFINE    BUILD S4            ;SC_S4  Z180 as replacement Z80 only
;#DEFINE    BUILD S5            ;SC_S5  Z180 (eg. SC111 plus SC119)
#DEFINE    BUILD S6            ;SC_S6  Z180 (eg. SC126)

;#DEFINE    BUILD T1            ;TomsSBC standard ROM

;#DEFINE    BUILD W1            ;SCWorkshop simulator - standard
;
;#DEFINE    BUILD Z1            ;Z280RC by Bill Shen 
;#DEFINE    BUILD Z2            ;Z80SBCRC by Bill Shen (framework only)


; **********************************************************************
; Configuration defaults

#INCLUDE    Config\Config_Standard.asm

; **********************************************************************
; For each value of BUILD include a suitable Build.asm file

#IF         BUILD = "0*"
#INCLUDE    Hardware\Custom\Build.asm
#ENDIF

#IF         BUILD = "C*"
#INCLUDE    Hardware\Z80sc\Build.asm
#ENDIF

#IF         BUILD = "F*"
#INCLUDE    Config\SC_F1\Build.asm
#ENDIF

#IF         BUILD = "L*"
#INCLUDE    Hardware\LiNC80\Build.asm
#ENDIF

#IF         BUILD = "Q9"
#INCLUDE    Config\Q9\Build.asm
#ENDIF

#IF         BUILD = "R*"
#INCLUDE    Hardware\RC2014\Build.asm
#ENDIF

#IF         BUILD = "S2"
#INCLUDE    Config\SC_S2\Build.asm
#ENDIF

#IF         BUILD = "S3"
#INCLUDE    Hardware\SC_S3\Build.asm
#ENDIF

#IF         BUILD = "S4"
#INCLUDE    Hardware\SC_S4\Build.asm
#ENDIF

#IF         BUILD = "S5"
#INCLUDE    Config\SC_S5\Build.asm
#ENDIF

#IF         BUILD = "S6"
#INCLUDE    Config\SC_S6\Build.asm
#ENDIF

#IF         BUILD = "T1"
#INCLUDE    Hardware\TomsSBC\Build.asm
#ENDIF

#IF         BUILD = "W1"
#INCLUDE    Config\Workshop\Build.asm
#ENDIF

#IF         BUILD = "Z1"
#INCLUDE    Hardware\Z280RC\Build.asm
#ENDIF

#IF         BUILD = "Z2"
#INCLUDE    Hardware\Z80SBCRC\Build.asm
#ENDIF






