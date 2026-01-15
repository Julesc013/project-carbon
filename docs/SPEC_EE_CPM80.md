# SPEC_EE_CPM80

Purpose
- Define the CP/M 2.x EE provider contract.

Scope
- Provider binding, guest load/run conventions, and deterministic behavior.

Internal layering
- JC-DOS host -> EE_CPM80 provider -> CP/M guest program.

Contracts and invariants
- EE_CPM80 implements the base SPEC_EE ABI and provider kind.
- Guest I/O is virtualized through host services.

Extension recipes
- Add CP/M compatibility flags via minor versions.

Versioning rules
- Major version mismatch is incompatible and must fail binding.
- Minor version mismatch follows the compatibility rules in the spec.

Determinism rules
- Guest-visible outputs are deterministic for identical inputs and storage.

Out of scope
- Full CP/M BIOS/BDOS behavior.

Canonical references
- source/runtime/ee_cpm80/ee_cpm80.c
- source/tests/conformance/ee/cpm80/ee_cpm80_conformance.c
- docs/SPEC_EE.md
