# SPEC_CPU_Z85

Purpose
- Define the Z85 CPU family contract and tier presentation.

Scope
- CPU tier identity, presentation rules, and core-level constraints.

Internal layering
- Z85 core -> discovery/CAPSET reporting -> OS-visible CPU contract.

Contracts and invariants
- Z85 presents P2 tier semantics (Z80 class) per the OS contract.
- Floating-point is external and not part of the CPU ISA contract.

Extension recipes
- Add optional feature bits via CAPSET and discovery tables.

Versioning rules
- CPU contract versioning follows the platform contract policy.

Determinism rules
- CPU-visible ordering and side effects are deterministic per contract.

Out of scope
- Micro-architectural implementation details and performance guarantees.

Canonical references
- docs/cpu/Z85.md
- hdl/cores/Z85/docs/Z85_v1.md
- source/common/spec/JC0_OS_CONTRACT.md
