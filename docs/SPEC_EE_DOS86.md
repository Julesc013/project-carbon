# SPEC_EE_DOS86

Purpose
- Define the DOS86 EE provider contract for MS-DOS style guests.

Scope
- Provider binding, guest load/run conventions, and deterministic behavior.

Internal layering
- JC-DOS host -> EE_DOS86 provider -> DOS guest program.

Contracts and invariants
- EE_DOS86 implements the base SPEC_EE ABI and provider kind.
- Guest I/O is virtualized through host services.

Extension recipes
- Add DOS86 feature flags and compatibility shims via minor versions.

Versioning rules
- Major version mismatch is incompatible and must fail binding.
- Minor version mismatch follows the compatibility rules in the spec.

Determinism rules
- Guest-visible outputs are deterministic for identical inputs and storage.

Out of scope
- Full DOS kernel behavior or driver stacks.

Canonical references
- source/runtime/ee_dos86/ee_dos86.c
- source/tests/conformance/ee/dos86/ee_dos86_conformance.c
- docs/SPEC_EE.md
