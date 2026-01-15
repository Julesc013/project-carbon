# SPEC_MODE

Purpose
- Define MODEUP/RETMD semantics and the mode-frame ABI.

Scope
- Mode transition rules, preservation requirements, and error reporting.

Internal layering
- Tier entry points -> MODEUP/RETMD -> mode-frame save/restore.

Contracts and invariants
- MODEUP is upgrade-only; RETMD returns to the prior tier.
- Mode-frame layout and preserved state are contract-defined.

Extension recipes
- Add new mode flags or frame fields via minor version updates.

Versioning rules
- Major version mismatch is incompatible and must fail binding.
- Minor version mismatch follows the compatibility rules in the spec.

Determinism rules
- Mode transitions must be deterministic for identical inputs.

Out of scope
- Micro-architectural implementation details.

Canonical references
- source/common/spec/SPEC_MODE.md
- hdl/spec/mode_switch.yaml
