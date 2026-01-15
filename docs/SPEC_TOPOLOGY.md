# SPEC_TOPOLOGY

Purpose
- Define the topology table layout and interpretation rules.

Scope
- Core counts, memory regions, and domain descriptors as exposed to firmware/OS.

Internal layering
- Topology table -> discovery pointer -> BIOS/OS consumption.

Contracts and invariants
- Table layout and entry types are stable and versioned.
- Memory region descriptors are authoritative for RAM/ROM/MMIO classification.

Extension recipes
- Add new entry types via minor version updates and reserved fields.

Versioning rules
- Major version mismatch is incompatible and must fail binding.
- Minor version mismatch follows the compatibility rules in the spec.

Determinism rules
- Topology reporting is deterministic for fixed discovery inputs.

Out of scope
- Platform-specific device driver policy.

Canonical references
- source/common/spec/SPEC_TOPOLOGY.md
