# SPEC_TOPOLOGY (v1.0)

Purpose
- Define CPU topology, tier hosting, and memory region tables.

Versioning
- Version format: major.minor.
- Major mismatch: reject and fail boot.
- Minor greater than supported: reject and fail boot.
- Minor lower or equal: accept; reserved fields remain reserved.

Binary layout
- Endianness: little-endian for all multi-byte fields.
- Alignment: 4-byte aligned headers and entries.

Topology header (JC_TOPOLOGY_HEADER_V1, 16 bytes)
- signature: u32 @0 = "CTOP" (0x504F5443)
- header_version: u16 @4 (must be 1)
- header_size: u16 @6 (must be 16)
- entry_size: u16 @8 (must be 32)
- entry_count: u16 @10
- total_size: u32 @12

Topology entry (JC_TOPOLOGY_ENTRY_V1, 32 bytes)
- socket_id: u16 @0
- cluster_id: u16 @2
- core_id: u16 @4
- thread_id: u16 @6
- cache_l1_id: u16 @8
- cache_l2_id: u16 @10
- cache_l3_id: u16 @12
- coherence_domain_id: u16 @14
- numa_node_id: u16 @16
- reserved0: u112 @18 (must be 0)

Tier host header (JC_TIER_HOST_HEADER_V1, 16 bytes)
- signature: u32 @0 = "CTRH" (0x48525443)
- header_version: u16 @4 (must be 1)
- header_size: u16 @6 (must be 16)
- entry_size: u16 @8 (must be 16)
- entry_count: u16 @10
- total_size: u32 @12

Tier host entry (JC_TIER_HOST_ENTRY_V1, 16 bytes)
- socket_id: u16 @0
- cluster_id: u16 @2
- core_id: u16 @4
- reserved0: u16 @6 (must be 0)
- tier_mask: u16 @8 (bit N => tier PN supported)
- reserved1: u16 @10 (must be 0)
- reserved2: u32 @12 (must be 0)

Memory region header (JC_MEM_REGION_HEADER_V1, 16 bytes)
- signature: u32 @0 = "CMEM" (0x4D454D43)
- header_version: u16 @4 (must be 1)
- header_size: u16 @6 (must be 16)
- entry_size: u16 @8 (must be 24)
- entry_count: u16 @10
- total_size: u32 @12

Memory region entry (JC_MEM_REGION_ENTRY_V1, 24 bytes)
- region_kind: u8 @0 (0=RAM, 1=ROM, 2=MMIO)
- region_attrs: u8 @1 (MEM_ATTR_* bits)
- reserved0: u16 @2 (must be 0)
- base_addr: u64 @4
- size_bytes: u64 @12
- reserved1: u32 @20 (must be 0)

MEM_ATTR bits (region_attrs)
- MEM_ATTR_CACHEABLE = bit 0
- MEM_ATTR_ORDERED = bit 1
- MEM_ATTR_IO_SPACE = bit 2
- MEM_ATTR_ACQUIRE = bit 3
- MEM_ATTR_RELEASE = bit 4

Invariants
- total_size equals header_size + entry_count * entry_size.
- Entries are contiguous; no gaps.
- Memory regions must not overlap for the same region_kind.
- tier_mask must only use bits 0-15.

Failure semantics
- Invalid signature, version, size, or total_size is fatal.
- Overlapping memory regions of the same kind are fatal.
