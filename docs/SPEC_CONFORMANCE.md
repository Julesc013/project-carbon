# SPEC_CONFORMANCE

Purpose
- Define the conformance transcript format and gating rules.

Scope
- Transcript headers, hash lines, PASS/FAIL rules, and allowed diffs.

Internal layering
- Conformance test -> transcript -> hash/CRC gate -> release decision.

Contracts and invariants
- Transcripts are canonical artifacts for reference targets.
- Header and hash lines must be stable across runs.

Extension recipes
- Add new transcript sections via versioned header lines.

Versioning rules
- Major version mismatch is incompatible and must fail the gate.
- Minor version mismatch follows the compatibility rules in the spec.

Determinism rules
- Transcripts must be deterministic for identical inputs.

Out of scope
- Performance benchmarking and profiling output.

Canonical references
- source/common/spec/SPEC_CONFORMANCE.md
- docs/VERIFICATION.md
