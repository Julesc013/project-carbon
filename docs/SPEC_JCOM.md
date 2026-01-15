# SPEC_JCOM

Purpose
- Define the JCOM program format and load policy.

Scope
- Header fields, load/entry rules, and exit conventions.

Internal layering
- Loader -> JCOM image -> execution environment.

Contracts and invariants
- Header fields are fixed and versioned by the spec.
- Exit convention is stable and must be honored by loaders.

Extension recipes
- Add optional TLV areas via minor version updates.

Versioning rules
- Major version mismatch is incompatible and must fail binding.
- Minor version mismatch follows the compatibility rules in the spec.

Determinism rules
- JCOM loading is deterministic for identical inputs.

Out of scope
- Language runtime semantics and guest OS policy.

Canonical references
- source/common/spec/SPEC_JCOM.md
