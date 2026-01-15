# SPEC_PAL

Purpose
- Define the Platform Adapter Layer (PAL) ABI and required services.

Scope
- PAL service vtables, required/optional services, and error mapping.

Internal layering
- Platform boot hooks -> PAL bind -> service vtables -> BIOS/OS.

Contracts and invariants
- PAL is the only layer that depends on platform boot details.
- Required services must be present or fail deterministically.

Extension recipes
- Add optional services and flags via minor version updates.

Versioning rules
- Major version mismatch is incompatible and must fail binding.
- Minor version mismatch follows the compatibility rules in the spec.

Determinism rules
- PAL outputs must be deterministic for identical inputs.

Out of scope
- Guest execution policy and device driver logic.

Canonical references
- source/common/spec/SPEC_PAL.md
- source/common/include/jc_pal.h
