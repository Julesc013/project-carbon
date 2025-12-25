# SPEC_BDT (v1.0)

Purpose
- Define the BIOS Device Table (BDT) binary layout for device discovery.

Versioning
- Version format: major.minor.
- Major mismatch: reject and fail boot.
- Minor greater than supported: reject and fail boot.
- Minor lower or equal: accept; reserved fields remain reserved.

Binary layout
- Endianness: little-endian for all multi-byte fields.
- Alignment: 4-byte aligned header/entries.

BDT header (JC_BDT_HEADER_V1, 16 bytes)
- signature: u32 @0 = "CBDT" (0x54444243)
- header_version: u16 @4 (must be 1)
- header_size: u16 @6 (must be 16)
- entry_size: u16 @8 (must be 64)
- entry_count: u16 @10
- total_size: u32 @12 (header + entries + routing table + footer)

BDT entry (JC_BDT_ENTRY_V1, 64 bytes)
- desc_version: u16 @0 (must be 1)
- desc_size_bytes: u16 @2 (must be 64)
- class_id: u16 @4
- subclass_id: u16 @6
- instance_id: u16 @8
- device_version: u16 @10
- caps0: u32 @12 (compatibility flags + class-specific fields)
- caps1: u32 @16 (turbo flags + class-specific fields)
- irq_route_offset: u16 @20 (offset from BDT base, 0 if none)
- irq_route_count: u16 @22 (0 if none)
- mmio_base: u64 @24 (0 if none)
- mmio_size: u32 @32 (0 if none)
- io_port_base: u32 @36 (0 if none)
- io_port_size: u16 @40 (0 if none)
- block_sector_size: u16 @42 (0 if not a block device)
- cai_queue_count: u16 @44 (0 if not CAI-capable)
- cai_doorbell_offset: u16 @46 (CSR offset, 0 if not applicable)
- aux_ptr: u64 @48 (0 if none)
- aux_size: u32 @56 (0 if none)
- aux_type: u16 @60 (0 if none)
- reserved0: u16 @62 (must be 0)

IRQ routing entry (JC_BDT_IRQ_ROUTE_V1, 8 bytes)
- domain_id: u16 @0
- irq_line: u16 @2
- flags: u16 @4 (IRQ_FLAG_* bits)
- reserved0: u16 @6 (must be 0)

BDT footer (JC_BDT_FOOTER_V1, 4 bytes)
- crc32: u32 @0 (CRC32 over BDT region excluding footer)

CRC32
- CRC32 (IEEE, poly 0x04C11DB7) with init 0xFFFFFFFF, reflected in/out,
  final XOR 0xFFFFFFFF.
- CRC32 covers bytes from the BDT header through the last routing entry;
  the footer is excluded.

Device class IDs
- DEVCLASS_CPU = 0x0001
- DEVCLASS_ACCEL = 0x0002
- DEVCLASS_UART = 0x0010
- DEVCLASS_PIO = 0x0012
- DEVCLASS_TIMER = 0x0013
- DEVCLASS_PIC = 0x0014
- DEVCLASS_DMA = 0x0020
- DEVCLASS_STORAGE = 0x0030

Compatibility caps (caps0)
- DEV_COMPAT_POLLING = bit 0
- DEV_COMPAT_IRQ = bit 1
- DEV_COMPAT_PORT_IO = bit 2
- DEV_COMPAT_MMIO = bit 3
- DEV_COMPAT_WAIT = bit 4

Turbo caps (caps1)
- DEV_TURBO_QUEUE = bit 0
- DEV_TURBO_DMA = bit 1
- DEV_TURBO_TIMESTAMPS = bit 2
- DEV_TURBO_PERF = bit 3
- DEV_TURBO_WATERMARK_IRQ = bit 4

Invariants
- total_size equals header_size + entry_count * entry_size + routing table bytes + footer size.
- irq_route_offset must be 0 or point within the BDT region.
- If mmio_size is nonzero, mmio_base must be nonzero.
- If io_port_size is nonzero, io_port_base must be nonzero.
- block_sector_size must be 512 or a multiple of 512.

Failure semantics
- Invalid signature, version, size, or CRC32 is fatal.
- Out-of-range offsets or sizes are fatal.
