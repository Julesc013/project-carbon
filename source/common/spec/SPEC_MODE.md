# SPEC_MODE (v1.0)

Purpose
- Define the MODEUP/RETMD contract, MODEFLAGS, trap causes, and the MODE ABI capsule.

Versioning
- Version format: major.minor.
- Major mismatch: reject and trap with MODE_TRAP_INVALID_TARGET.
- Minor greater than supported: reject and trap with MODE_TRAP_INVALID_TARGET.
- Minor lower or equal: accept; reserved bits remain reserved.

Binary layout
- Endianness: little-endian for all multi-byte fields.
- Alignment: 4-byte aligned structures.

MODEFLAGS (u8)
- Bit 0: MODEFLAG_STRICT (reset 1)
- Bit 1: MODEFLAG_INTMASK (reset 0)
- Bits 2-7: reserved, must be 0

MODE frame (JC_MODEFRAME_V1, 16 bytes)
- previous_tier: u8 @0
- previous_modeflags: u8 @1
- reserved0: u16 @2 (must be 0)
- reserved1: u32 @4 (must be 0)
- return_pc: u64 @8

MODE ABI capsule (JC_MODE_ABI_V1, 32 bytes)
- version: u16 @0 (must be 1)
- size_bytes: u16 @2 (must be 32)
- target_tier: u8 @4
- reserved0: u8 @5 (must be 0)
- flags: u16 @6 (bit0 = INTMASK request)
- entry_vector: u64 @8 (target entry address)
- return_pc: u64 @16 (written by MODEUP on success)
- error_code: u32 @24 (MODE_TRAP_* on failure)
- reserved1: u32 @28 (must be 0)

ABI and calling convention
- The ABI capsule pointer is passed in HL for all tiers; the capsule must reside
  in the low 64 KiB address space.
- Stack alignment: SP is 2-byte aligned at MODEUP entry and preserved by MODEUP/RETMD.
- Preserved registers: all architecturally visible general registers and flags
  are preserved across MODEUP and RETMD (PC changes by definition).
- Interrupts are masked for the duration of the atomic transition.
- Post-transition interrupt state:
  - If MODE_ABI flags INTMASK is set, interrupts remain masked in the new tier.
  - Otherwise, the pre-transition interrupt enable state is restored.

Invariants
- MODEUP is upgrade-only; target_tier must be strictly greater than current tier.
- RETMD is the only architectural downgrade path.
- MODEUP/RETMD must flush prefetch/decode state.
- Modestack minimum depth is 4; overflow/underflow must trap.

Failure semantics
- Invalid target tier, invalid entry vector, privilege violation, or modestack
  overflow/underflow must trap and set CSR_CAUSE to MODE_TRAP_*.
- If a MODE ABI capsule is supplied, error_code is written with MODE_TRAP_* before trap.
