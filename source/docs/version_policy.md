# Version Policy

Purpose
- Define version semantics for JC-BIOS, JC-DOS, and host tools.
- Define the v1.0 lock conditions.

Version format
- Project versions are major.minor.
- Patch numbers are allowed for documentation and tooling only.

Semantics
- Major: incompatible contract or ABI change (reject older data).
- Minor: backward-compatible additions using reserved fields.
- Patch: no contract or ABI impact.

Compatibility
- Firmware and OS reject contract major mismatches and minor versions newer
  than supported.
- Older minor versions must be accepted if the consumer supports the same major.

v1.0 lock
- SPEC_*.md contents and binary layouts are frozen at v1.0.
- Autogen headers are part of the locked ABI surface.
- Conformance transcript formats and stable output strings are frozen at v1.0.
- Any change that modifies contracts, on-wire layouts, or transcript outputs
  requires a major bump.
- Post-v1.0 patches may change docs, tooling, and tests only when behavior is
  unchanged.
