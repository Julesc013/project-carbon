# SPEC_TIERS (v1.0)

Purpose
- Define the canonical compatibility ladder IDs and tier values reported by discovery.

Versioning
- Version format: major.minor.
- Major mismatch: reject and fail boot.
- Minor greater than supported: reject and fail boot.
- Minor lower or equal: accept; reserved values remain reserved.

Binary layout
- Ladder ID: u8.
- Tier value: u8.
- Endianness: not applicable (single-byte fields).

Ladder IDs
- TIER_LADDER_Z80 = 0
- TIER_LADDER_AM95 = 1

CPU ladder (TIER_LADDER_Z80)
- P0 = 0 (8080)
- P1 = 1 (8085)
- P2 = 2 (Z80)
- P3 = 3 (Z180)
- P4 = 4 (eZ80 ADL)
- P5 = 5 (Z280)
- P6 = 6 (Z380)
- P7 = 7 (Z480)

FPU ladder (TIER_LADDER_AM95)
- P0 = 0 (Am9511)
- P1 = 1 (Am9512-plus)
- P2 = 2 (Am9513)
- P3 = 3 (Am9514)
- P4 = 4 (Am9515)

Invariants
- Reset always starts in P0 for every ladder.
- Presented tiers are strict semantic environments; optional behavior is expressed by feature bits.
- MODEUP is monotonic upgrade-only; RETMD is the only downgrade path.

Failure semantics
- If a ladder ID is unknown or a tier value is out of range for the ladder, the discovery
  record is invalid and boot must fail with JC_E_DISCOVERY_BAD_VERSION.
