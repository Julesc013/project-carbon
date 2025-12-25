# SPEC_DEV_PIC (v1.0)

Purpose
- Define the CarbonKIO PIC compatibility register ABI.

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
- IRQ_ENABLE @0x0070 (RW)
- IRQ_PENDING @0x0074 (RO)
- IRQ_MASK @0x0078 (RW)

IRQ source bits (pending/enable/mask)
- bit 0: UART_RX_WATERMARK
- bit 1: UART_TX_WATERMARK
- bit 4: TIMER0_EXPIRED
- bit 5: TIMER1_EXPIRED

Invariants
- IRQ_PENDING reflects current source conditions.
- Clearing a source condition clears its pending bit.
- IRQ delivery is optional; polling must always work.

Failure semantics
- Reads of undefined offsets return 0.
- Writes to undefined offsets are ignored.
