; **********************************************************************
; **  Device Driver                             by Stephen C Cousins  **
; **  Hardware: SC_S2 (SC114 and compatibles)                         **
; **  Interface: Serial bit-bang                                      **
; **********************************************************************

; This module is the driver for the SC_S2 bit-bang serial port.
;
; The hardware interface consists of:
; Transmit data output     port <kTxPrt>   bit 0
; Request to send output   port <kRtsPrt>  bit 0
; Receive data input       port <kRxPrt>   bit 7
;
; The serial data format is standard TTL serial:
;
; ---+     +-----+-----+-----+-----+-----+-----+-----+-----+-----+-   1
;    |start|  0  |  1  |  2  |  3  |  4  |  5  |  6  |  7  | stop
;    +-----+-----+-----+-----+-----+-----+-----+-----+-----+          0
;
; At 9600 baud each bit takes 104.167us
; 0.5 bits takes 52.083us, 1.5 bits takes 156.25us


; **********************************************************************
; **  Constants
; **********************************************************************

; Must be defined in hardware manager module. eg:
;kTxPrt:    .EQU 0x28           ;Transmit output is bit zero
;kRtsPrt:   .EQU 0x20           ;/RTS output is bit zero
;kRxPrt:    .EQU 0x28           ;Receive input is bit 7


; **********************************************************************
; **  Driver code
; **********************************************************************

            .CODE


; Initialise 
;   On entry: No parameters required
;   On exit:  AF unspecified
;             BC DE HL IX IY I AF' BC' DE' HL' preserved
; Set Tx output to idle state (high)
SCS2_bbInit:
            LD   A, 1           ;Transmit high vlaue
            OUT  (kTxPrt), A    ;Output to transmit data port
            RET


; Transmit byte 
;   On entry: A = Byte to be transmitted via bit-bang serial port
;   On exit:  If character output successful (eg. device was ready)
;               NZ flagged and A != 0
;             BC DE HL IX IY I AF' BC' DE' HL' preserved
SCS2_bbTx:  PUSH BC             ;Preserve BC
            LD   C, A           ;Store character to be transmitted
            XOR  A
            OUT  (kTxPrt), A    ;Begin start bit
            OUT  (kTxPrt), A    ;Just here to add a little extra delay
            LD   A, C           ;Restore character to be transmitted
            LD   C, 10          ;Bit count including stop
@Bit:       LD   B, 56          ;Delay time [7]
@Delay:     DJNZ @Delay         ;Loop until end of delay [13/8]
            NOP                 ;Tweak delay time [4]
            OUT  (kTxPrt), A    ;Output current bit [11]
            SCF                 ;Ensure stop bit is logic 1 [4]
            RRA                 ;Rotate right through carry [4]
            DEC  C              ;Decrement bit count [4]
            JR   NZ,@Bit        ;Repeat until zero [12/7]
            OR   0xFF           ;Return success A !=0 and flag NZ
            POP  BC             ;Restore BC
            RET


; Receive byte 
;   On entry: No parameters required
;   On exit:  A = Byte received via bit-bang serial port
;             NZ flagged if character input
;             BC DE HL IX IY I AF' BC' DE' HL' preserved
; The receive input must be on bit 7 of the port kRxPrt
SCS2_bbRx:  PUSH BC             ;Preserve BC
            XOR  A              ;Enable RTS line so
            OUT  (kRtsPrt), A   ;  terminal can send a character
            LD   B, 10
@Delay:     DJNZ @Delay         ;Wait a while
            INC  A              ;Disable RTS line so
            OUT  (kRtsPrt), A   ;  terminal will not send a character
@Wait:      IN   A, (kRxPrt)    ;Read receive port [11]
            AND  0x80           ;Test receive input [7]
            JR   Z, @Begin      ;Abort if no start bit [12/7]
            DJNZ @Wait          ;Timeout?
            POP  BC             ;Restore BC
            XOR  A              ;Return Z as no character received
            RET
@Begin:     PUSH DE             ;Preserve DE
            LD   E, 8           ;Prepare bit counter
            LD   B, 82          ;Delay 1.5 bits [7]
@Bit:       DJNZ @Bit           ;Loop until end of delay [13/8]
            IN   A, (kRxPrt)    ;Read receive port [11]
            AND  0x80           ;Mask data bit and clear carry [7]
            RR   C              ;Rotate result byte right [8]
            OR   C              ;OR input bit with result byte [4]
            LD   C, A           ;Store current result byte [4]
            LD   B, 55          ;Delay 1 bit [7]
            DEC  E              ;Decrement bit counter [4]
            JR   NZ, @Bit       ;Repeat until zero [12/7]
@Stop:      DJNZ @Stop          ;Wait for stop bit
            OR   0xFF           ;Return NZ as character received
            LD   A, C           ;Return byte received
            POP  DE             ;Restore DE
            POP  BC             ;Restore BC
            RET


; **********************************************************************
; **  End of driver                                                   **
; **********************************************************************




