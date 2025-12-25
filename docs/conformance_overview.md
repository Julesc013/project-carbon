# Conformance Overview (JC0)

Purpose
- Summarize the conformance transcript mechanism used for parity gating.

Key points
- Conformance transcripts are authoritative, byte-for-byte artifacts.
- Each transcript includes contract versions, CAPSET CRC32, and BDT CRC32.
- The final CRC32 covers the entire transcript body and is mandatory.

Reference targets
- SIM_REF, FPGA_REF, and HW_REF1 must emit transcripts with identical bytes.
- PROFILE_SOC_RETRO is required for v1 reference targets.

Specification
- See `source/common/spec/SPEC_CONFORMANCE.md` for the exact format.

PAL conformance
- `source/tests/conformance/pal/pal_conformance.c` validates PAL boot, block I/O,
  CP/M FS signature, and transcript CRC.
- PALs may emit RESULT SKIP if the platform is unsupported.

EE conformance
- `source/tests/conformance/ee/cpm80/ee_cpm80_conformance.c`.
- `source/tests/conformance/ee/dos86/ee_dos86_conformance.c`.
- Negative tests use `NEG_UNSUPPORTED` and `NEG_ILLEGAL` fault paths.
