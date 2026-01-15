# SPEC_FS_CPMX

Purpose
- Define the CP/M-style filesystem contract (CPMX).

Scope
- Directory layout, naming rules, allocation units, and extent behavior.

Internal layering
- Block device -> CPMX filesystem -> OS/EE consumers.

Contracts and invariants
- Layout and naming rules are fixed by the spec.
- Reserved fields remain zero and are not repurposed without versioning.

Extension recipes
- Add optional metadata via minor version updates and reserved fields.

Versioning rules
- Major version mismatch is incompatible and must fail binding.
- Minor version mismatch follows the compatibility rules in the spec.

Determinism rules
- Filesystem behavior is deterministic for identical inputs and media.

Out of scope
- Host filesystem mapping or journaling features.

Canonical references
- source/common/spec/SPEC_FS_CPMX.md
