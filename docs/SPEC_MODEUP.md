# SPEC_MODEUP

Purpose
- Provide a single entry point for MODEUP/RETMD rules.

Scope
- References the canonical MODE contract and mode-frame ABI.

Internal layering
- Tier entry points -> MODEUP/RETMD -> mode-frame save/restore.

Contracts and invariants
- MODEUP is upgrade-only; RETMD returns to the prior tier.

Extension recipes
- See docs/SPEC_MODE.md for mode flag and frame extension rules.

Versioning rules
- See docs/SPEC_MODE.md for version compatibility requirements.

Determinism rules
- Mode transitions are deterministic for identical inputs.

Out of scope
- Micro-architectural implementation details.

Canonical references
- docs/SPEC_MODE.md
- source/common/spec/SPEC_MODE.md
- hdl/spec/mode_switch.yaml
