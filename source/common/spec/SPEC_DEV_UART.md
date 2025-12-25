# SPEC_DEV_UART (v1.0)

Purpose
- Define the CarbonKIO UART compatibility register ABI.

Versioning
- Version format: major.minor.
- Major mismatch: reject and fail boot.
- Minor greater than supported: reject and fail boot.
- Minor lower or equal: accept; reserved bits remain reserved.

Binary layout
- Register width: 32 bits.
- Access: byte-addressable, little-endian.
- Offsets are from the device's compatibility base (I/O or MMIO).

Register map (compatibility)
- UART_DATA @0x0000 (RW, low byte only)
- UART_STATUS @0x0004 (RO)
- UART_CTRL @0x0008 (RW)
- UART_RX_COUNT @0x000C (RO)
- UART_TX_COUNT @0x0010 (RO)
- UART_TS_LO @0x0014 (RO)
- UART_TS_HI @0x0018 (RO)
- UART_WATERMARKS @0x001C (RW)

UART_STATUS bits
- bit 0: RX_AVAIL (1 if RX FIFO not empty)
- bit 1: TX_READY (1 if TX can accept data)
- bit 2: RX_OVERFLOW (sticky)
- bit 3: TX_OVERFLOW (sticky)

UART_CTRL bits
- bit 0: ENABLE (1 enables TX)
- bit 3: TS_EN (1 enables RX timestamp capture)
- bit 4: CLR_ERR (write 1 clears RX/TX overflow; self-clears)

UART_WATERMARKS
- bits 7:0 = RX watermark
- bits 15:8 = TX watermark

Invariants
- UART_DATA reads return 0 if RX FIFO is empty.
- UART_DATA writes are ignored when ENABLE is 0.
- RX/TX overflow bits remain set until CLR_ERR is written.
- Polling via UART_STATUS must always work; IRQs are optional.

Failure semantics
- Reads of undefined offsets return 0.
- Writes to undefined offsets are ignored.
