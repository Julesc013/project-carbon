# SPEC_PROFILES

Purpose
- Define system profile IDs and required platform features.

Scope
- Profile enumeration, required devices, and capability expectations.

Internal layering
- Profile ID -> platform feature requirements -> BIOS/OS behavior.

Contracts and invariants
- Profile IDs are stable and reported via discovery.
- Required devices for a profile must be present or fail deterministically.

Extension recipes
- Add new profile IDs via minor version updates and capability gating.

Versioning rules
- Major version mismatch is incompatible and must fail binding.
- Minor version mismatch follows the compatibility rules in the spec.

Determinism rules
- Profile selection is deterministic for fixed discovery inputs.

Out of scope
- Platform-specific implementation details.

Canonical references
- source/common/spec/SPEC_PROFILES.md
