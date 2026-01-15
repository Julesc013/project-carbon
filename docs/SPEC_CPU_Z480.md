# SPEC_CPU_Z480

Purpose
- Define the Z480 CPU family contract and tier presentation.

Scope
- CPU tier identity, privilege model exposure, and core-level constraints.

Internal layering
- Z480 core -> discovery/CAPSET reporting -> OS-visible CPU contract.

Contracts and invariants
- Z480 presents P7 tier semantics as defined by the architecture contract.
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
- docs/cpu/Z480.md
- hdl/cores/Z480/docs/Z480.md
- source/common/spec/JC0_OS_CONTRACT.md
