# SPEC_TIERS

Purpose
- Define the CPU and FPU tier ladders and their semantic meaning.

Scope
- Tier identifiers, ordering rules, and presentation requirements.

Internal layering
- Tier definitions -> discovery/CAPSET reporting -> OS-visible behavior.

Contracts and invariants
- Tier ordering is fixed and monotonic.
- Presented tiers must match the contract definitions.

Extension recipes
- Reserve new tiers via versioned extensions without reordering.

Versioning rules
- Major version mismatch is incompatible and must fail binding.
- Minor version mismatch follows the compatibility rules in the spec.

Determinism rules
- Tier presentation is deterministic for fixed discovery inputs.

Out of scope
- Performance expectations or micro-architectural details.

Canonical references
- source/common/spec/SPEC_TIERS.md
