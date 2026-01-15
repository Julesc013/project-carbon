# SPEC_IRQ

Purpose
- Define IRQ routing encoding and delivery expectations.

Scope
- IRQ routing fields used by BDT entries and PIC devices.

Internal layering
- Device interrupt source -> PIC routing -> CPU IRQ delivery.

Contracts and invariants
- IRQ routing encoding is stable and contract-defined.
- Optional ACK/EOI paths are capability-gated.

Extension recipes
- Add new routing fields via minor version updates.

Versioning rules
- Major version mismatch is incompatible and must fail binding.
- Minor version mismatch follows the compatibility rules in the spec.

Determinism rules
- IRQ routing behavior is deterministic for identical inputs.

Out of scope
- Vendor-specific priority schemes outside the contract.

Canonical references
- source/common/spec/SPEC_IRQ.md
