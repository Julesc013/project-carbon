# SPEC_CAPSET

Purpose
- Define the normalized capability set (CAPSET) exposed to firmware and OS.

Scope
- CPU/FPU tiers, profile ID, feature bitmaps, and pointers to topology and BDT.

Internal layering
- Discovery block -> CAPSET synthesis -> OS-facing capability record.

Contracts and invariants
- CAPSET fields are authoritative for presented tiers and profile ID.
- Reserved fields remain zero and are not repurposed without versioning.

Extension recipes
- Add new feature bits and optional pointer fields via minor version updates.

Versioning rules
- Major version mismatch is incompatible and must fail binding.
- Minor version mismatch follows the compatibility rules in the spec.

Determinism rules
- CAPSET synthesis is deterministic for fixed discovery inputs.

Out of scope
- Device driver policy and platform-specific probing.

Canonical references
- source/common/spec/SPEC_CAPSET.md
- hdl/spec/discovery.yaml
