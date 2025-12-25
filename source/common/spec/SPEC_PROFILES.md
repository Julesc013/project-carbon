# SPEC_PROFILES (v1.0)

Purpose
- Define system configuration profiles reported by discovery and honored by BIOS/DOS.

Versioning
- Version format: major.minor.
- Major mismatch: reject and fail boot.
- Minor greater than supported: reject and fail boot.
- Minor lower or equal: accept; reserved values remain reserved.

Binary layout
- Profile ID: u8.
- Endianness: not applicable (single-byte field).

Profile IDs
- PROFILE_CPU_ONLY = 0
- PROFILE_MCU = 1
- PROFILE_SOC_RETRO = 2
- PROFILE_SOC_WORKSTATION = 3

Invariants
- Profile is configuration, not a tier.
- Profile reported via discovery must be honored by BIOS/DOS.
- PROFILE_SOC_RETRO is the JC0 primary profile for v1 reference targets.

Failure semantics
- Unknown or reserved profile IDs are fatal; BIOS must fail with JC_E_BOOT_UNSUPPORTED_PROFILE.
