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
