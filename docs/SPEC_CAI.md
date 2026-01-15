# SPEC_CAI

Purpose
- Define the Carbon Accelerator Interface (CAI) queue and doorbell contract.

Scope
- Descriptor queues, completion signaling, and memory ordering expectations.

Internal layering
- Host driver -> CAI queues -> accelerator device.

Contracts and invariants
- Queue ownership and producer/consumer indices are contract-defined.
- Completion ordering and visibility rules are explicit and deterministic.

Extension recipes
- Add new opcodes or queue features via capability bits and minor revisions.

Versioning rules
- Major version mismatch is incompatible and must fail binding.
- Minor version mismatch follows the compatibility rules in the spec.

Determinism rules
- Completion ordering is deterministic for identical inputs.

Out of scope
- Accelerator algorithm details and performance guarantees.

Canonical references
- source/common/spec/SPEC_CAI.md
- hdl/spec/cai.yaml
