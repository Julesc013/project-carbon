# Determinism

Purpose
- Define determinism guarantees and limits across firmware, OS, PAL, EE, and tooling.

Deterministic inputs
- Contract generation and rendering are deterministic; see scripts/gen_arch.*.
- PAL and EE outputs must be deterministic for identical inputs and storage.
- Conformance transcripts are canonical outputs for reference targets.

Sources of non-determinism (disallowed unless documented)
- Wall clock time, randomness, or timing jitter that affects outputs.
- Probe-based behavior that depends on host timing or external state.

Explicit allowances
- Optional services are gated by capability flags and configuration.
- Fault injection is deterministic and transcripted; see source/common/include/jc_fault.h.

References
- docs/error_model.md
- source/common/spec/SPEC_CONFORMANCE.md
- source/common/spec/SPEC_PAL.md
- source/common/spec/SPEC_EE.md
