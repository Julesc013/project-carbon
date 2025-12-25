# SPEC_DISCOVERY (v1.0)

Purpose
- Define the canonical discovery mechanism and discovery table layout.

Versioning
- Version format: major.minor.
- Major mismatch: reject and fail boot.
- Minor greater than supported: reject and fail boot.
- Minor lower or equal: accept; reserved fields remain reserved.

Discovery mechanism (v1)
- The boot ROM reads a BSP anchor located at a BSP-defined fixed address.
- The BSP anchor contains a 64-bit pointer to the discovery table.
- Pointer value 0 means discovery is absent and boot must fail.

BSP anchor (JC_BSP_ANCHOR_V1, 24 bytes)
- signature: u32 @0 = "CBSP" (0x50534243)
- version: u16 @4 (must be 1)
- size_bytes: u16 @6 (must be 24)
- discovery_ptr: u64 @8 (physical address of discovery table)
- reserved0: u64 @16 (must be 0)

Discovery table (JC_DISCOVERY_TABLE_V1, 64 bytes)
- signature: u32 @0 = "CDSC" (0x43534443)
- table_version: u16 @4 (must be 1)
- table_size: u16 @6 (must be 64)
- cpu_ladder_id: u8 @8
- fpu_ladder_id: u8 @9
- presented_cpu_tier: u8 @10
- presented_fpu_tier: u8 @11
- profile_id: u8 @12
- reserved0: u24 @13 (must be 0)
- topology_table_ptr: u64 @16
- bdt_ptr: u64 @24
- limits_table_ptr: u64 @32
- cpu_feature_bitmap_ptr: u64 @40
- fpu_feature_bitmap_ptr: u64 @48
- peripheral_feature_bitmap_ptr: u64 @56

Feature bitmap (JC_FEATURE_BITMAP_V1, 16 bytes)
- word0: u32 @0
- word1: u32 @4
- word2: u32 @8
- word3: u32 @12

Limits table (JC_LIMITS_TABLE_V1, 32 bytes)
- queue_submit_depth: u32 @0
- queue_complete_depth: u32 @4
- contexts: u16 @8
- vector_lanes: u16 @10
- tensor_rank: u16 @12
- reserved0: u16 @14 (must be 0)
- max_cores: u16 @16
- max_threads: u16 @18
- reserved1: u96 @20 (must be 0)

CPUID/CAPS leaf IDs
- CPUID_LEAF_VENDOR = 0x00000000
- CPUID_LEAF_ID = 0x00000001
- CPUID_LEAF_DISCOVERY = 0x00000002
- CPUID_LEAF_FEATURES0 = 0x00000003
- CPUID_LEAF_DEVICE_TABLE = 0x00000004
- CPUID_LEAF_FEATURES1 = 0x00000005
- CPUID_LEAF_FEATURES2 = 0x00000006
- CPUID_LEAF_CACHE0 = 0x00000010
- CPUID_LEAF_TOPOLOGY = 0x00000011
- CPUID_LEAF_ACCEL0 = 0x00000020
- CPUID_LEAF_ERRATA0 = 0x00000030

Invariants
- Endianness: little-endian for all multi-byte fields.
- Pointers are physical addresses; 0 means absent.
- Discovery is canonical; CPUID/CAPS are mirrors of the discovery table.

Failure semantics
- Invalid signature, version, or size in BSP anchor or discovery table is fatal.
- A null discovery pointer in the BSP anchor is fatal.
- CPUID/CAPS unknown leaf IDs must return all zeros.
