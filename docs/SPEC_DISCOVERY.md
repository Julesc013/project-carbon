# SPEC_DISCOVERY

Purpose
- Define the discovery block format and access rules.

Scope
- Discovery pointer location, block layout, and required fields.

Internal layering
- Boot ROM -> discovery pointer -> discovery block -> CAPSET/BDT/topology.

Contracts and invariants
- Discovery contents are authoritative for presented tiers and profiles.
- Pointers must be valid and aligned as specified by the contract.

Extension recipes
- Add optional fields via minor version updates with reserved space.

Versioning rules
- Major version mismatch is incompatible and must fail binding.
- Minor version mismatch follows the compatibility rules in the spec.

Determinism rules
- Discovery data is deterministic for a fixed boot configuration.

Out of scope
- Platform-specific probing policy outside PAL.

Canonical references
- source/common/spec/SPEC_DISCOVERY.md
- hdl/spec/discovery.yaml
