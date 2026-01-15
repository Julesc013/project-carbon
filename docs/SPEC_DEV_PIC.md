# SPEC_DEV_PIC

Purpose
- Define the PIC device-class register and IRQ routing contract.

Scope
- Interrupt routing fields, polling read behavior, and optional ACK/EOI paths.

Internal layering
- BDT entry -> PIC register block -> driver.

Contracts and invariants
- Polling read is always valid; IRQ support is capability-gated.
- IRQ routing encoding follows the IRQ spec.

Extension recipes
- Add optional enable/disable/ack features via minor version updates.

Versioning rules
- Major version mismatch is incompatible and must fail binding.
- Minor version mismatch follows the compatibility rules in the spec.

Determinism rules
- IRQ routing behavior is deterministic for identical inputs.

Out of scope
- Vendor-specific priority schemes not described in capabilities.

Canonical references
- source/common/spec/SPEC_DEV_PIC.md
- docs/SPEC_IRQ.md
