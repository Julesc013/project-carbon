# SPEC_JCOM (v1.0)

Purpose
- Define the JCOM program image format and exit convention.

Versioning
- Version format: major.minor.
- Major mismatch: reject and fail load.
- Minor greater than supported: reject and fail load.
- Minor lower or equal: accept; reserved fields remain reserved.

Binary layout
- Endianness: little-endian for all multi-byte fields.
- Alignment: 4-byte aligned header.

Header (JC_JCOM_HEADER_V1, 48 bytes)
- signature: u32 @0 = "JCOM" (0x4D4F434A)
- header_version: u16 @4 (must be 1)
- header_size: u16 @6 (must be 48)
- min_cpu_tier: u8 @8
- reserved0: u8 @9 (must be 0)
- flags: u16 @10
- load_policy: u32 @12 (JCOM_LOAD_FIXED=0)
- load_addr: u64 @16
- entry_offset: u32 @24
- bss_size: u32 @28
- image_size: u32 @32
- tlv_size: u32 @36
- crc32: u32 @40
- reserved1: u32 @44 (must be 0)

TLV extension area
- TLV region begins immediately after the fixed header.
- Each TLV entry:
  - type: u16
  - length: u16 (bytes of value)
  - value: byte[length]
  - entries are padded to 4-byte alignment.
- tlv_size is the total TLV region size in bytes.

CRC32
- CRC32 (IEEE, poly 0x04C11DB7) with init 0xFFFFFFFF, reflected in/out,
  final XOR 0xFFFFFFFF.
- CRC32 covers header + payload + TLV region; crc32 field is treated as 0.

Exit convention
- Program returns to loader via RET.
- Return code is placed in A (low 8 bits) on return.

Standard I/O model
- stdin/stdout/stderr map to the console UART in v1.

Invariants
- entry_offset is relative to load_addr.
- image_size excludes bss_size.

Failure semantics
- Invalid signature, version, or CRC32 is fatal.
- If min_cpu_tier is greater than the presented CPU tier, load must fail with JC_E_EXEC_UNSUPPORTED_TIER.
