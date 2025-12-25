# Version Policy

Purpose
- Define project version semantics for JC-BIOS, JC-DOS, and host tools.

Version format
- Project versions are major.minor.
- Optional patch numbers are allowed for documentation/tooling fixes only.

Semantics
- Major: incompatible contract or ABI change (reject older data).
- Minor: backward-compatible additions (reserved fields become defined).
- Patch: no contract or ABI impact.

Pre-1.0 policy
- v0.x is pre-release but still adheres to the major/minor rules above.
- JC0 is locked at v0.0 and must not introduce runtime functionality.

Compatibility
- Firmware and OS must reject contract major mismatches and minor versions
  newer than the consumer supports.
