# SPEC_DEV_UART

Purpose
- Define the UART device-class register and behavior contract.

Scope
- Register access, status bits, and minimal console I/O behavior.

Internal layering
- BDT entry -> UART register block -> driver.

Contracts and invariants
- Polling read/write semantics must be available.
- Optional IRQ behavior is capability-gated.

Extension recipes
- Add optional FIFO or flow-control fields via minor version updates.

Versioning rules
- Major version mismatch is incompatible and must fail binding.
- Minor version mismatch follows the compatibility rules in the spec.

Determinism rules
- UART behavior is deterministic for identical inputs.

Out of scope
- Vendor-specific extensions not declared in capabilities.

Canonical references
- source/common/spec/SPEC_DEV_UART.md
