# SPEC_EE

Purpose
- Define the Execution Environment (EE) ABI for hosted guests.

Scope
- EE lifecycle, service binding, and error handling.

Internal layering
- JC-DOS host -> EE provider -> guest program boundary.

Contracts and invariants
- EE providers implement a common ABI defined by jc_ee.
- Host-visible behavior is deterministic for identical inputs.

Extension recipes
- Add new EE kinds via versioned provider descriptors.

Versioning rules
- Major version mismatch is incompatible and must fail binding.
- Minor version mismatch follows the compatibility rules in the spec.

Determinism rules
- EE outputs must be deterministic for identical inputs and storage.

Out of scope
- Guest OS internals and application semantics.

Canonical references
- source/common/spec/SPEC_EE.md
- source/common/include/jc_ee.h
