# SPEC_CAPSET (v1.0)

Purpose
- Define the normalized JC_CAPSET structure produced by BIOS from raw discovery.

Versioning
- Version format: major.minor.
- Major mismatch: reject and fail boot.
- Minor greater than supported: reject and fail boot.
- Minor lower or equal: accept; reserved fields remain reserved.

Binary layout (JC_CAPSET_V1, 128 bytes)
- signature: u32 @0 = "CCAP" (0x50414343)
- version: u16 @4 (must be 1)
- size_bytes: u16 @6 (must be 128)
- cpu_ladder_id: u8 @8
- fpu_ladder_id: u8 @9
- presented_cpu_tier: u8 @10
- presented_fpu_tier: u8 @11
- profile_id: u8 @12
- reserved0: u24 @13 (must be 0)
- cpu_features: u32[4] @16
- fpu_features: u32[4] @32
- periph_features: u32[4] @48
- topology_table_ptr: u64 @64
- bdt_ptr: u64 @72
- limits_table_ptr: u64 @80
- mem_region_table_ptr: u64 @88
- tier_host_table_ptr: u64 @96
- max_devices: u16 @104
- max_dma_segments: u16 @106
- max_bdt_entries: u16 @108
- max_irq_routes: u16 @110
- reserved1: u32 @112 (must be 0)
- reserved2: u32[3] @116 (must be 0)

Invariants
- Endianness: little-endian for all multi-byte fields.
- Feature bitmaps mirror discovery table contents.
- Pointers are physical addresses; 0 means absent.
- Limits fields are authoritative for BIOS/DOS policy in the absence of device-specific overrides.

Failure semantics
- Invalid signature, version, or size is fatal; consumers must reject the capset.
