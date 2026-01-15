# SPEC_BDT

Purpose
- Define the BIOS Device Table (BDT) binary layout and device entry semantics.

Scope
- BDT header, entry list, class identifiers, and per-entry metadata consumed by
  firmware and OS.

Internal layering
- Discovery pointer -> BDT header -> entry array -> class-specific aux data.

Contracts and invariants
- BDT is the authoritative source for device addresses and capabilities.
- Entries are classed and versioned; reserved fields must be zero.
- BIOS/OS must not hardcode device bases outside the BDT.

Extension recipes
- Add new device classes via new class IDs and class-versioned aux data.
- Bump minor versions for compatible field additions.

Versioning rules
- Major version mismatch is incompatible and must fail binding.
- Minor version mismatch follows the compatibility rules in the spec.

Determinism rules
- BDT synthesis is deterministic for a fixed platform configuration.

Out of scope
- Device driver behavior and runtime policy.

Canonical references
- source/common/spec/SPEC_BDT.md
- hdl/spec/bdt.yaml
- hdl/spec/bdt_schema.yaml
