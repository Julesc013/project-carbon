# SPEC_DEV_STORAGE_IDEPIO

Purpose
- Define the IDE/CF PIO storage device-class contract.

Scope
- Task file register mapping, required commands, and error reporting.

Internal layering
- BDT entry -> storage register block -> driver.

Contracts and invariants
- 512-byte sectors are required.
- READ/WRITE sector operations follow the defined timeout rules.

Extension recipes
- Add optional DMA or feature commands via minor version updates.

Versioning rules
- Major version mismatch is incompatible and must fail binding.
- Minor version mismatch follows the compatibility rules in the spec.

Determinism rules
- Storage behavior is deterministic for identical inputs and media.

Out of scope
- SD/SATA/USB semantics outside the IDE/CF PIO contract.

Canonical references
- source/common/spec/SPEC_DEV_STORAGE_IDEPIO.md
