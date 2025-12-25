# SPEC_DEV_TIMER (v1.0)

Purpose
- Define the CarbonKIO timer/tick compatibility register ABI.

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
- TICK_LO @0x0040 (RO)
- TICK_HI @0x0044 (RO)
- TIMER0_LOAD @0x0048 (RW)
- TIMER0_VALUE @0x004C (RO)
- TIMER0_CTRL @0x0050 (RW)
- TIMER0_STATUS @0x0054 (RW, write clears)
- TIMER1_LOAD @0x0058 (RW)
- TIMER1_VALUE @0x005C (RO)
- TIMER1_CTRL @0x0060 (RW)
- TIMER1_STATUS @0x0064 (RW, write clears)

TIMERx_CTRL bits
- bit 0: ENABLE
- bit 1: AUTO_RELOAD
- bit 2: LOAD (write 1 to load VALUE from LOAD)

TIMERx_STATUS bits
- bit 0: EXPIRED (write any value to clear)

Tick frequency publication
- For timer devices, BDT caps0 bits 31:0 report tick_hz.

Invariants
- TICK is a 64-bit monotonic counter.
- TIMERx_VALUE decrements when ENABLE is set.
- EXPIRED is set when VALUE reaches 0.

Failure semantics
- Reads of undefined offsets return 0.
- Writes to undefined offsets are ignored.
