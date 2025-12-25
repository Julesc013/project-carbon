# Conformance Overview (v2.0)

Purpose
- Summarize the conformance transcript mechanism used for parity gating.

Key points
- Conformance transcripts are authoritative, byte-for-byte artifacts.
- Each transcript includes contract versions, CAPSET CRC32, and BDT CRC32.
- The final CRC32 covers the entire transcript body and is mandatory.
- v1.0 suites must continue to pass unchanged as v1.1-1.3 features are added.

Suites
- BIOS: v0.1-0.6 cover boot, monitor, MODEUP, storage/FS, and JCOM.
- DOS: v0.7-1.0 cover boot, file I/O, and execution.
- DOS v1.1 adds perf cache/fastmem checks.
- DOS v1.2 adds CAI/FPU checks (soft fallback and mock CAI).
- DOS v1.3 adds display checks (VT100 baseline, optional local display hash).
- DOS v1.4 adds personality session checks (native vs legacy, nested open/close).
- BIOS v1.7 adds storage robustness checks (retries, persistent failures, stress).
- DOS v1.8 adds IRQ parity checks (polling vs IRQ transcripts must match).
- DOS v2.0 adds PROFILE_MCU checks (optional storage, minimal shell).

Reference targets
- SIM_REF is the functional reference and must emit golden transcripts.
- FPGA_REF and HW_REF1 must compile and emit stable serial transcripts.

Specification
- See `source/common/spec/SPEC_CONFORMANCE.md` for the exact format.
