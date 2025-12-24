; **********************************************************************
; **  Z180 Support                              by Stephen C Cousins  **
; **  BIOS: RC_Z180_native                                            **
; **********************************************************************


; **********************************************************************
; **  Z180 register constants
; **********************************************************************

kZ180:      .EQU kZ180Base      ;Z180 internal register base address

CNTLA0:     .EQU kZ180 + 0x00   ;ASCI Channel Control Register A chan 0
CNTLA1:     .EQU kZ180 + 0x01   ;ASCI Channel Control Register A chan 1
CNTLB0:     .EQU kZ180 + 0x02   ;ASCI Channel Control Register B chan 0
CNTLB1:     .EQU kZ180 + 0x03   ;ASCI Channel Control Register B chan 1
STAT0:      .EQU kZ180 + 0x04   ;ASCI Status Register channel 0
STAT1:      .EQU kZ180 + 0x05   ;ASCI Status Register channel 1
TDR0:       .EQU kZ180 + 0x06   ;ASCI Transmit Data Register channel 0
TDR1:       .EQU kZ180 + 0x07   ;ASCI Transmit Data Register channel 1
RDR0:       .EQU kZ180 + 0x08   ;ASCI Receive Register channel 0
RDR1:       .EQU kZ180 + 0x09   ;ASCI Receive Register channel 1
CNTR:       .EQU kZ180 + 0x0A   ;CSI/O Contol/Status Register
TRDR:       .EQU kZ180 + 0x0B   ;CSI/O Transmit/Receive Data Register
TMDR0L:     .EQU kZ180 + 0x0C   ;Timer Data Register Channel 0 Low
TMDR0H:     .EQU kZ180 + 0x0D   ;Timer Data Register Channel 0 High
RLDR0L:     .EQU kZ180 + 0x0E   ;Timer Reload Register Channel 0 Low
RLDR0H:     .EQU kZ180 + 0x0F   ;Timer Reload Register Channel 0 High
TCR:        .EQU kZ180 + 0x10   ;Timer Control Register

ASCI0:      .EQU kZ180 + 0x12   ; ASCI Extension Control Register 0
ASCI1:      .EQU kZ180 + 0x13   ; ASCI Extension Control Register 1
TMDR1L:     .EQU kZ180 + 0x14   ;Timer Data Register Channel 1 Low
TMDR1H:     .EQU kZ180 + 0x15   ;Timer Data Register Channel 1 High
RLDR1L:     .EQU kZ180 + 0x16   ;Timer Reload Register Channel 1 Low
RLDR1H:     .EQU kZ180 + 0x17   ;Timer Reload Register Channel 1 High
FRC:        .EQU kZ180 + 0x18   ;Free Running Counter (read only)

ASTC0L:     .EQU kZ180 + 0x1A   ;ASCI Time Constant Register ch 0 Low
ASTC0H:     .EQU kZ180 + 0x1B   ;ASCI Time Constant Register ch 0 High
ASTC1L:     .EQU kZ180 + 0x1C   ;ASCI Time Constant Register ch 1 Low
ASTC1H:     .EQU kZ180 + 0x1D   ;ASCI Time Constant Register ch 1 High
CMR:        .EQU kZ180 + 0x1E   ;Clock Multiplier Register
CCR         .EQU kZ180 + 0x1F   ;CPU Control Register
SAR0L:      .EQU kZ180 + 0x20   ;DMA Source Address Register ch 0 Low
SAR0H:      .EQU kZ180 + 0x21   ;DMA Source Address Register ch 0 High
SAR0B:      .EQU kZ180 + 0x22   ;DMA Source Address Register ch 0 B
DAR0L:      .EQU kZ180 + 0x23   ;DMA Destination Address Reg ch 0 Low
DAR0H:      .EQU kZ180 + 0x24   ;DMA Destination Address Reg ch 0 High
DAR0B:      .EQU kZ180 + 0x25   ;DMA Destination Address Reg ch 0 B
BCR0L:      .EQU kZ180 + 0x26   ;DMA Byte Count Register channel 0 Low
BCR0H:      .EQU kZ180 + 0x27   ;DMA Byte Count Register channel 0 High
MAR1L:      .EQU kZ180 + 0x28   ;DMA Memory Address Register ch 1 Low
MAR1H:      .EQU kZ180 + 0x29   ;DMA Memory Address Register ch 1 High
MAR1B:      .EQU kZ180 + 0x2A   ;DMA Memory Address Register ch 1 B
IAR1L:      .EQU kZ180 + 0x2B   ;DMA I/O Address Register channel 1 Low
IAR1H:      .EQU kZ180 + 0x2C   ;DMA I/O Address Register channel 1 High
IAR1B:      .EQU kZ180 + 0x2D   ;DMA I/O Address Register channel 1 B
BCR1L:      .EQU kZ180 + 0x2E   ;DMA Byte Count Register channel 1 Low
BCR1H:      .EQU kZ180 + 0x2F   ;DMA Byte Count Register channel 1 High
DSTAT:      .EQU kZ180 + 0x30   ;DMA Status Register
DMODE:      .EQU kZ180 + 0x31   ;DMA Mode Register
DCNTL:      .EQU kZ180 + 0x32   ;DMA/WAIT Control Register
IL:         .EQU kZ180 + 0x33   ;Interrupt Vector Register
ITC:        .EQU kZ180 + 0x34   ;INT/TRAP Control Register

RCR:        .EQU kZ180 + 0x36   ;Refresh Control Register

CBR:        .EQU kZ180 + 0x38   ;MMU Control Base Register
BBR:        .EQU kZ180 + 0x39   ;MMU Bank Base Register
CBAR:       .EQU kZ180 + 0x3A   ;MMU Common/Bank Register

OMCR:       .EQU kZ180 + 0x3E   ;Operation Mode Control Register
ICR:        .EQU kZ180 + 0x3F   ;I/O Control Register

; **********************************************************************
; Serial status register bits

ST_RDRF:    .EQU 7              ;Receive data register Full
ST_TDRE:    .EQU 1              ;Transmit data register empty


; **********************************************************************
; **  Public functions                                                **
; **********************************************************************

            .CODE

Z180Init:   

; ALREADY DONE DURING SELF TEST
; Position Z180 internal I/O at 0xC0 to 0xFF
            ;LD   A,0xC0        ;Start of Z180 internal I/O
            ;OUT0 (ICR),A

; ALREADY DONE DURING SELF TEST
; Initialise Memory Management Unit (MMU)
; This maps logical (64k) memory to physical (1M) memory
; Common(0) 0x0000 to 0x7FFF -> 0x00000 to 0x07FFF
; Bank      0x8000 to 0xFFFF -> 0x80000 to 0xFFFFF
; Common(1) 0x8000 to 0xFFFF -> 0x80000 to 0xFFFFF
            ;LD   A,0x80        ;Physical address = A x 0x1000
            ;OUT0 (BBR), A      ;Bank Base Register = 0x80
            ;OUT0 (CBR), A      ;Common(1) Base Register = 0x80
; Both Bank and Common(1) start at logical address 0x8000
            ;LD   A,0x88        ;Logical address = Nibble x 0x1000
            ;OUT0 (CBAR), A     ;Both start at 0x8000

; Initialise Z180 serial port 0
;
; Baud rate = PHI/(baud rate divider x prescaler x sampling divider)
;   PHI = CPU clock input / 1 = 18.432/1 MHz = 18.432 MHz
;   Baud rate divider (1,2,4,8,16,32,or 64) = 1
;   Prescaler (10 or 30) = 10
;   Sampling divide rate (16 or 64) = 16
; Baud rate = 18,432,00 / ( 1 x 10 x 16) = 18432000 / 160 = 115200 baud
;
; Control Register A for channel 0 (CNTLA0)
;   Bit 7 = 0    Multiprocessor Mode Enable (MPE)
;   Bit 6 = 1    Receiver Enable (RE)
;   Bit 5 = 1    Transmitter Enable (TE)
;   Bit 4 = 0    Request to Send Output (RTS0) (0 = Low, 1 = High)
;   Bit 3 = 0    Multiprocessor Bit Receive/Error Flag (MPBR) (0 = Reset)
;   Bit 2 = 1    Data Format (0 = 7-bit, 1 = 8-bit)
;   Bit 1 = 0    Parity (0 = No Parity, 1 = Parity Enabled)
;   Bit 0 = 0    Stop Bits (0 = 1 Stop Bit, 1 = 2 Stop Bits)
            LD   A, 0b01100100
            OUT0 (CNTLA0), A
; And the same for channel 1 
            OUT0 (CNTLA1), A

; Control Register B for channel 0 (CNTLB0)
;   Bit 7 = 0    Multiprocessor Bit Transmit (MPBT)
;   Bit 6 = 0    Multiprocessor Mode (MP)
;   Bit 5 = 0    Clear to Send/Prescale (CTC/PS) (0 = PHI/10, 1 = PHI/30)
;   Bit 4 = 0    Parity Even Odd (PEO) (0 = Even, 1 = Odd)
;   Bit 3 = 0    Divide Ratio (DR) (0 = divide 16, 1 = divide 64)
;   Bit 2 = 000  Source/Speed Select (SS2-SS0)
;    to 0        (0 = /1, 1 = /2, .. 6 = /64, 7 = External clock)
            LD   A, 0b00000000
            OUT0 (CNTLB0), A
; And the same for channel 1 
            OUT0 (CNTLB1), A

; Extension Control Register (ASCI0) [Z8S180/L180-class processors only)
;   Bit 7 = 0    Receive Interrupt Inhibit (0 = Inhibited, 1 = Enabled)
;   Bit 6 = 1    DCD0 Disable (0 = DCD0 Auto-enable Rx, 1 = Advisory)
;   Bit 5 = 1    CTS0 Disable (0 = CTS0 Auto-enable Tx, 1 = Advisory)
;   Bit 4 = 0    X1 Bit Clock (0 = CKA0/16 or 64, 1 = CKA0 is bit clock)
;   Bit 3 = 0    BRG0 Mode (0 = As S180, 1 = Enable 16-BRG counter)
;   Bit 2 = 0    Break Feature (0 = Enabled, 1 = Disabled)
;   Bit 1 = 0    Break Detect (0 = On, 1 = Off)
;   Bit 0 = 0    Send Break (0 = Normal transmit, 1 = Drive TXA Low)
            LD   A, 0b01100000
            OUT0 (ASCI0), A
; And the same for channel 1 
            OUT0 (ASCI1), A

; Refresh Control Register (RCR)
;   Bit 7 = 0    Refresh Enable (REFE) (0 = Disabled, 1 = Enabled)
;   Bit 6 = 0    Refresh Wait (REFW) (0 = 2 clocksm 3 = 3 clocks)
;   Bit 1-0 = 0  Cycle Interval (CYC1-0) 
            LD   A, 0b00000000
            OUT0 (RCR), A       ;Turn off memory refresh

; DMA/WAIT Control Register (DCNTL)
;   Bit 7-6 = 00 Memory Wait Insertion (MWI1-0) (0 to 3 wait states)
;   Bit 5-4 = 11 I/O Wait Insertion (IWI1-0) (0 to 3 wait states) 
;   Bit 3 = 0    DMA Request Sense ch 1 (DMS1) (0 = Level, 1 = Edge)
;   Bit 2 = 0    DMA Request Sense ch 0 (DMS0) (0 = Level, 1 = Edge)
;   Bit 1 = 0    DMA Channel 1 Mode (DIM1) (0 = Mem to I/O, 1 = I/O to Mem)
;   Bit 0 = 0    DMA Channel 0 Mode (DIM0) (0 = MARI+1, 1 = MARI-1)
;   Bit 3-2 = 00 DMA Request Sense (DMS1-0) (0 = Level, 1 = Edge)
            LD   A, 0b00110000
            OUT0 (DCNTL), A     ;Maximum wait states for I/O and Memory

; Operating Mode Control Register (OMCR)
;   Bit 7 = 0    M1 Enable (M1E) (1 = Default, 0 = Z80 compatibility mode)
;   Bit 6 = 0    M1 Temporary Enable (M1TE) (1 = Default, 0 = Z80 mode)
;   Bit 5 = 0    I/O Compatibility (IOC) (1 = Default, 0 = Z80 mode)
;   Bits 4-0 = 0 Reserved
            LD   A, 0b00000000
            OUT0 (OMCR), A      ;Select Z80 compatibility mode

; CPU Control Register (CCR)
;   Bit 7 = 1    CPU Clock Divide (0 = Divide 2, 1 = Divide 1)
;   Bit 6+3 = 0  Standy/Idle Mode (00 = No Standby, 01 = ...)
;   Bit 5 = 0    Bus Request Exit (0 = Ignore in standby, 1 = Exit on BR)
;   Bit 4 = 0    PHI Clock Drive (0 = Standard, 1 = 33%)
;   Bit 3+6 = 0  Standy/Idle Mode (00 = No Standby, 01 = ...)
;   Bit 2 = 0    External I/O Drive (0 = Standard, 1 = 33%)
;   Bit 1 = 0    Control Signal Drive (0 = Standard, 1 = 33%)
;   Bit 0 = 0    Address and Data Drive (0 = Standard, 1 = 33%)
            LD   A, 0b10000000
            OUT0 (CCR), A

; Set reload registers for 1ms timer
; Timer input clock is PHI/20 = 18,432,000MHz/20 = 921.6kHz
; Relead time to give 1ms timer is 921.6 (0x039A when rounded up)
            LD   A,0x9A
            OUT0 (RLDR0L),A
            LD   A,0x03
            OUT0 (RLDR0H),A

; Timer Control Register
;   Bit 7 = 0    Timer 1 interrupt flag
;   Bit 6 = 0    Timer 0 interrupt flag
;   Bit 5 = 0    Timer 1 interrupt enable
;   Bit 4 = 0    Timer 0 interrupt enable
;   Bit 3-2 = 00 Inhibit timer output on A18/Tout
;   Bit 1 = 0    Timer 1 down count enable
;   Bit 0 = 1    Timer 0 down count enable
            LD   A,0b00000001
            OUT0 (TCR),A

            RET


; **********************************************************************
; **  Z180's internal serial port 0 drivers (port A)


; Receive byte
;   On entry: No parameters required
;   On exit:  A = Character input from the device
;             NZ flagged if character input
;             BC DE HL IX IY I AF' BC' DE' HL' preserved
Z180RxByteA:
            IN0  A,(STAT0)      ;Read serial port status register
            BIT  ST_RDRF,A      ;Receive register full?
            RET  Z              ;Return Z as no character available
            IN0  A,(RDR0)       ;Read data byte
            RET


; Transmit byte
;   On entry: A = Character to be output to the device
;   On exit:  If character output successful (eg. device was ready)
;               NZ flagged and A != 0
;             If character output failed (eg. device busy)
;               Z flagged and A = Character to output
;             BC DE HL IX IY I AF' BC' DE' HL' preserved
Z180TxByteA:
            PUSH BC             ;Preserve BC
            IN0  B,(STAT0)      ;Read serial port status register
            BIT  ST_TDRE,B      ;Transmit register empty?
            POP  BC             ;Restore BC
            RET  Z              ;Return Z as character not output
            OUT0 (TDR0), A      ;Write byte to serial port
            OR   0xFF           ;Return success A=0xFF and NZ flagged
            RET


; **********************************************************************
; **  Z180's internal serial port 1 drivers (port B)


; Receive byte
;   On entry: No parameters required
;   On exit:  A = Character input from the device
;             NZ flagged if character input
;             BC DE HL IX IY I AF' BC' DE' HL' preserved
Z180RxByteB:
            IN0  A,(STAT1)      ;Read serial port status register
            BIT  ST_RDRF,A      ;Receive register full?
            RET  Z              ;Return Z as no character available
            IN0  A,(RDR1)       ;Read data byte
            RET


; Transmit byte
;   On entry: A = Character to be output to the device
;   On exit:  If character output successful (eg. device was ready)
;               NZ flagged and A != 0
;             If character output failed (eg. device busy)
;               Z flagged and A = Character to output
;             BC DE HL IX IY I AF' BC' DE' HL' preserved
Z180TxByteB:
            PUSH BC             ;Preserve BC
            IN0  B,(STAT1)      ;Read serial port status register
            BIT  ST_TDRE,B      ;Transmit register empty?
            POP  BC             ;Restore BC
            RET  Z              ;Return Z as character not output
            OUT0 (TDR1), A      ;Write byte to serial port
            OR   0xFF           ;Return success A=0xFF and NZ flagged
            RET


; **********************************************************************
; **  Z180's internal baud rate generator

; Common baud rates:
; 115200, 57600, 38400, 19200, 9600, 4800, 2400, 1200, 600, 300
;
; Baud rate = PHI/(baud rate divider x prescaler x sampling divider)
;   PHI = CPU clock input / 1 = 18.432/1 MHz = 18.432 MHz
;   Baud rate divider (1,2,4,8,16,32,or 64) = 1
;   Prescaler (10 or 30) = 10
;   Sampling divide rate (16 or 64) = 16
; Baud rate = 18,432,00 / ( 1 x 10 x 16) = 18432000 / 160 = 115200 baud
;
; Possible baud rates and dividers based on 18.432 MHz clock:
;  +----------+-----------+-----------+-----------+-------------+
;  |  Serial  |    Total  | Sampling  | Prescaler |   Baudrate  |
;  |    Baud  |  Divider  |  Divider  |   Divider |    Divider  |
;  +----------+-----------+-----------+-----------+-------------+
;  |  230400* |       80  |       16  |       10  |        n/a  |
;  |  115200  |      160  |       16  |       10  |          1  |
;  |   57600  |      320  |       16  |       10  |          2  |
;  |   38400  |      480  |       16  |       30  |          1  |
;  |   19200  |      960  |       16  |       30  |          2  |
;  |   14400  |     1280  |       16  |       10  |          8  |
;  |    9600  |     1920  |       16  |       30  |          4  |
;  |    4800  |     3840  |       16  |       30  |          8  |
;  |    2400  |     7680  |       16  |       30  |         16  |
;  |    1200  |    15360  |       16  |       30  |         32  |
;  |     600  |    30720  |       16  |       30  |         64  |
;  |     300* |    61440  |       16  |       30  |        n/a  |
;  +----------+-----------+-----------+-----------+-------------+
;  |   19200* |      960  |       64  |       30  |        n/a  |
;  |   14400  |     1280  |       64  |       10  |          2  |
;  |    9600  |     1920  |       64  |       30  |          1  |
;  |    4800  |     3840  |       64  |       30  |          2  |
;  |    2400  |     7680  |       64  |       30  |          4  |
;  |    1200  |    15360  |       64  |       30  |          8  |
;  |     600  |    30720  |       64  |       30  |         16  |
;  |     300  |    61440  |       64  |       30  |         32  |
;  |     150  |   122880  |       64  |       30  |         64  |
;  +----------+-----------+-----------+-----------+-------------+
; * = Can not be generated baud rate in this configuration.
;
; We use the following:
;  +----------+-----------+-----------+-----------+-------------+
;  |  115200  |      160  |       16  |       10  |          1  |
;  |   57600  |      320  |       16  |       10  |          2  |
;  |   38400  |      480  |       16  |       30  |          1  |
;  |   19200  |      960  |       16  |       30  |          2  |
;  |   14400  |     1280  |       16  |       10  |          8  |
;  +----------+-----------+-----------+-----------+-------------+
;  |    9600  |     1920  |       64  |       30  |          1  |
;  |    4800  |     3840  |       64  |       30  |          2  |
;  |    2400  |     7680  |       64  |       30  |          4  |
;  |    1200  |    15360  |       64  |       30  |          8  |
;  |     600  |    30720  |       64  |       30  |         16  |
;  |     300  |    61440  |       64  |       30  |         32  |
;  |     150  |   122880  |       64  |       30  |         64  |
;  +----------+-----------+-----------+-----------+-------------+


; **********************************************************************
; Hardware: Set baud rate
;   On entry: No parameters required
;   On entry: A = Baud rate code
;             C = Console device number (1 to 6)
;   On exit:  IF successful: (ie. valid device and baud code)
;               A != 0 and NZ flagged
;             BC DE HL not specified
;             IX IY I AF' BC' DE' HL' preserved
; A test is made for valid a device number and baud code.
;  +----------+-------------+-----------+-----------+-------------+
;  |  Serial  |  Baud rate  | Sampling  | Prescaler |   Baudrate  |
;  |    Baud  |       code  |  Divider  |   Divider |    Divider  |
;  +----------+-------------+-----------+-----------+-------------+
;  |  230400* |  1 or 0x23  |       16  |       10  |        n/a  |
;  |  115200  |  2 or 0x11  |       16  |       10  |          1  |
;  |   57600  |  3 or 0x57  |       16  |       10  |          2  |
;  |   38400  |  4 or 0x38  |       16  |       30  |          1  |
;  |   19200  |  5 or 0x19  |       16  |       30  |          2  |
;  |   14400  |  6 or 0x14  |       16  |       10  |          8  |
;  |    9600  |  7 or 0x96  |       64  |       30  |          1  |
;  |    4800  |  8 or 0x48  |       64  |       30  |          2  |
;  |    2400  |  9 or 0x24  |       64  |       30  |          4  |
;  |    1200  | 10 or 0x12  |       64  |       30  |          8  |
;  |     600  | 11 or 0x60  |       64  |       30  |         16  |
;  |     300  | 12 or 0x30  |       64  |       30  |         32  |
;  |     150  | 13 or 0x15  |       64  |       30  |         64  |
;  +----------+-------------+-----------+-----------+-------------+
H_SetBaud:
; Search for baud rate in table
; A = Baud rate code  (not verified)
; C = Console device number (1 to 6)  (not verified)
            LD   HL,@BaudTable  ;Start of baud rate table
            LD   B,13           ;Number of table entries
@Search:    CP   (HL)           ;Record for required baud rate?
            JR   Z,@Found       ;Yes, so go get time constant
            CP   B              ;Record number = baud rate code?
            JR   Z,@Found       ;Yes, so go get time constant
            INC  HL             ;Point to next record
            DJNZ @Search        ;Repeat until end of table
@Failed:    XOR  A              ;Return failure (A=0 and Z flagged)
            RET                 ;Abort as invalid baud rate
; Found location in table
; B = Baud code (1 to 13)  (verified)
; C = Console device number (1 to 6)  (not verified)
; (HL) = Serial hardware settings  (verified)
@Found:     DEC  C              ;Decrement device to range 0 to 5
            LD   A,C            ;Get device number (0 to 5)
            CP   2              ;Valid device number? (0 to 1)
            JR   NC,@Failed     ;No, so abourt
; B = Baud code (1 to 13)  (verified)
; C = Console device number - 1 (0 to 1)  (verified)
            LD   HL,@SettingsTable-1
            LD   E,B            ;Get baud rate code (1 to 13)
            LD   D,0
            ADD  HL,DE          ;Calculate address in table
            XOR  A              ;Clear in case of unsupported rate
            BIT  7,(HL)         ;Supported rate?
            RET  Z              ;No, so failure (A=0 and Z flagged)
; B = Baud code (1 to 13)  (verified)
; C = Console device number - 1 (0 to 1)  (verified)
; (HL) = Serial hardware CNTLB# register value
            LD   A,C            ;Get serial port number (0 or 1)
            OR   A              ;Port 0 ?
            JR   NZ,@Port1      ;No, so skip
            LD   A,(HL)         ;Get time serial hardware settings
            OUT0 (CNTLB0),A     ;Set port 0 baud rate
            JR   @BaudSet       ;Go return success
@Port1:     LD   A,(HL)         ;Get time serial hardware settings
            OUT0 (CNTLB1),A     ;Set port 1 baud rate
@BaudSet:   OR   0xFF           ;Return success (A=0xFF and NZ flagged)
            RET
;
; Baud rate table 
; Position in table matches value of short baud rate code (1 to 13)
; The table data bytes is the long baud rate code (eg. 0x96 for 9600)
@BaudTable: .DB  0x15           ;13 =    150
            .DB  0x30           ;12 =    300
            .DB  0x60           ;11 =    600
            .DB  0x12           ;10 =   1200
            .DB  0x24           ; 9 =   2400
            .DB  0x48           ; 8 =   4800
            .DB  0x96           ; 7 =   9600
            .DB  0x14           ; 6 =  14400
            .DB  0x19           ; 5 =  19200
            .DB  0x38           ; 4 =  38400
            .DB  0x57           ; 3 =  57600
            .DB  0x11           ; 2 = 115200
            .DB  0x23           ; 1 = 230400
;
; Serial hardware register settings table
; Settings to generate supported baud rates:
;  +----------+-------------+-----------+-----------+-------------+
;  |  Serial  |  Baud rate  | Sampling  | Prescaler |   Baudrate  |
;  |    Baud  |       code  |  Divider  |   Divider |    Divider  |
;  +----------+-------------+-----------+-----------+-------------+
;  |  230400* |  1 or 0x23  |       16  |       10  |        n/a  |
;  |  115200  |  2 or 0x11  |       16  |       10  |          1  |
;  |   57600  |  3 or 0x57  |       16  |       10  |          2  |
;  |   38400  |  4 or 0x38  |       16  |       30  |          1  |
;  |   19200  |  5 or 0x19  |       16  |       30  |          2  |
;  |   14400  |  6 or 0x14  |       16  |       10  |          8  |
;  |    9600  |  7 or 0x96  |       64  |       30  |          1  |
;  |    4800  |  8 or 0x48  |       64  |       30  |          2  |
;  |    2400  |  9 or 0x24  |       64  |       30  |          4  |
;  |    1200  | 10 or 0x12  |       64  |       30  |          8  |
;  |     600  | 11 or 0x60  |       64  |       30  |         16  |
;  |     300  | 12 or 0x30  |       64  |       30  |         32  |
;  |     150  | 13 or 0x15  |       64  |       30  |         64  |
;  +----------+-------------+-----------+-----------+-------------+
; The table data bytes are the Z180's CNTLB# register value:
;   bit 5 = prescaler, 0 = /10, 1 = /30
;   bit 3 = sampling divider, 0 = /16, 1 = /64
;   bits 0 to 2 = baud rate divider 0 = /1, 1 = /2, ... 6 = /64
;   bit 7 is set for supported baud rates
@Sam16      .EQU 0 + 128
@Sam64      .EQU 8 + 128
@Pre10      .EQU 0
@Pre30      .EQU 32
@Div1       .EQU 0
@Div2       .EQU 1
@Div4       .EQU 2
@Div8       .EQU 3
@Div16      .EQU 4
@Div32      .EQU 5
@Div64      .EQU 6
@SettingsTable:                 ;Code,  Baud,  Sample, Prescal, BRDivide
            .DB  0              ; 1 = 230400 (not supported)
            .DB  @Sam16 + @Pre10 + @Div1  ; 2 = 115200
            .DB  @Sam16 + @Pre10 + @Div2  ; 3 =  57600
            .DB  @Sam16 + @Pre30 + @Div1  ; 4 =  38400
            .DB  @Sam16 + @Pre30 + @Div2  ; 5 =  19200
            .DB  @Sam16 + @Pre10 + @Div8  ; 6 =  14400
            .DB  @Sam64 + @Pre30 + @Div1  ; 7 =   9600
            .DB  @Sam64 + @Pre30 + @Div2  ; 8 =   4800
            .DB  @Sam64 + @Pre30 + @Div4  ; 9 =   2400
            .DB  @Sam64 + @Pre30 + @Div8  ;10 =   1200
            .DB  @Sam64 + @Pre30 + @Div16 ;11 =    600
            .DB  @Sam64 + @Pre30 + @Div32 ;12 =    300
            .DB  @Sam64 + @Pre30 + @Div64 ;13 =    150


; **********************************************************************
; **  Z180's internal timer 0

; Poll timer
;   On entry: No parameters required
;   On exit:  If 1ms event to be processed NZ flagged and A != 0
;             BC DE HL IX IY I AF' BC' DE' HL' preserved
; This function polls a hardware timer and returns a flag is a
; 1ms event needs processing.
H_PollT2:   IN0  A,(TMDR0H)
            IN0  A,(TCR)
            AND  A,0x40
            RET


; **********************************************************************
; **  Public workspace (in RAM)                                       **
; **********************************************************************

            .DATA














