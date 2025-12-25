# SPEC_FS_CPMX (v1.0)

Purpose
- Define the CPMX filesystem (CP/M-like extent FS) on-disk layout.

Versioning
- Version format: major.minor.
- Major mismatch: reject and fail mount.
- Minor greater than supported: reject and fail mount.
- Minor lower or equal: accept; reserved fields remain reserved.

Binary layout
- Endianness: little-endian for all multi-byte fields.
- Alignment: superblock 4-byte aligned, directory entries 2-byte aligned.

Superblock (JC_CPMX_SUPERBLOCK_V1, 64 bytes)
- signature: u32 @0 = "CPMX" (0x584D5043)
- version: u16 @4 (must be 1)
- size_bytes: u16 @6 (must be 64)
- sector_size: u16 @8 (>= 512, multiple of 512)
- sectors_per_block: u16 @10 (power of two, >= 1)
- dir_entry_count: u16 @12
- reserved0: u16 @14 (must be 0)
- total_sectors: u32 @16
- dir_start_lba: u32 @20
- data_start_lba: u32 @24
- alloc_block_count: u32 @28
- volume_id: u32 @32
- flags: u32 @36 (CPMX_FLAGS bits)
- crc32: u32 @40 (CRC32 over superblock with crc32 set to 0)
- reserved1: u32 @44 (must be 0)
- reserved2: u32[4] @48 (must be 0)

Directory entry (JC_CPMX_DIR_ENTRY_V1, 32 bytes)
- user: u8 @0 (0-15 valid, 0xE5 means free)
- name: u8[8] @1 (ASCII uppercase, space padded)
- ext: u8[3] @9 (ASCII uppercase, space padded)
- flags: u8 @12 (CPMX_FLAGS bits)
- extent: u8 @13 (0-based extent index)
- reserved0: u8 @14 (must be 0)
- record_count: u8 @15 (count of 128-byte records in this extent)
- block_ptrs: u16[8] @16 (allocation block numbers, 1-based; 0 means unused)

CPMX_FLAGS
- READ_ONLY = bit 0
- SYSTEM = bit 1

Directory layout
- Directory region starts at dir_start_lba and is dir_entry_count * 32 bytes.
- Directory region is rounded up to full sectors; bytes beyond the last entry are 0.

Allocation units
- block_size = sector_size * sectors_per_block bytes.
- Allocation blocks are numbered 1..alloc_block_count.
- Block 0 is reserved and indicates unused in block_ptrs.

Naming rules
- name/ext characters are ASCII A-Z, 0-9, '_' or '-'.
- Unused name/ext characters are padded with 0x20 (space).
- The dot between name and ext is implicit; ext may be all spaces.

File length
- Each extent describes up to 8 blocks.
- record_count counts 128-byte records in this extent.
- File size is the sum of full extents plus record_count of the final extent.

CRC32
- CRC32 (IEEE, poly 0x04C11DB7) with init 0xFFFFFFFF, reflected in/out,
  final XOR 0xFFFFFFFF.
- crc32 field is treated as 0 during calculation.

Invariants
- total_sectors, dir_start_lba, and data_start_lba are within device bounds.
- data_start_lba is >= dir_start_lba.
- alloc_block_count * block_size does not exceed total_sectors * sector_size.
- Reserved fields must be 0.

Failure semantics
- Invalid signature, version, size, or CRC32 is fatal; volume must be rejected.
- Invalid name/ext characters are fatal; volume must be rejected.
