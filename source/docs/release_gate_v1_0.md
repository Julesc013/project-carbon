# Release Gate v1.0

Purpose
- Define the required checks before declaring a v1.0 release.

Gate checks
- Spec hash manifest matches `source/common/spec/spec_hashes_v1_0.txt`.
- Autogen headers match genspec output.
- Conformance transcripts match golden references.

Inputs
- Spec manifest: `source/common/spec/spec_hashes_v1_0.txt`.
- Defs list: `source/common/spec/defs/defs.lst`.
- Autogen headers:
  - `source/common/include/jc_contracts_autogen.h`
  - `source/common/include/jc_offsets_autogen.h`
- Golden transcripts:
  - BIOS: `source/firmware/JC-BIOS/tests/conformance/v0_1_boot/golden.txt`
  - BIOS: `source/firmware/JC-BIOS/tests/conformance/v0_2_monitor/golden.txt`
  - BIOS: `source/firmware/JC-BIOS/tests/conformance/v0_3_modeup/golden.txt`
  - BIOS: `source/firmware/JC-BIOS/tests/conformance/v0_4_devmodel/golden.txt`
  - BIOS: `source/firmware/JC-BIOS/tests/conformance/v0_5_fs_ops/golden.txt`
  - BIOS: `source/firmware/JC-BIOS/tests/conformance/v0_6_jcom/golden.txt`
  - DOS: `source/os/JC-DOS/tests/conformance/v0_7_boot/golden.txt`
  - DOS: `source/os/JC-DOS/tests/conformance/v0_8_fileops/golden.txt`
  - DOS: `source/os/JC-DOS/tests/conformance/v0_9_hardening/golden.txt`
  - DOS: `source/os/JC-DOS/tests/conformance/v1_0_release/golden.txt`
- Candidate transcripts (expected locations):
  - `build/transcripts/jc_bios_v0_1.txt`
  - `build/transcripts/jc_bios_v0_2.txt`
  - `build/transcripts/jc_bios_v0_3.txt`
  - `build/transcripts/jc_bios_v0_4.txt`
  - `build/transcripts/jc_bios_v0_5.txt`
  - `build/transcripts/jc_bios_v0_6.txt`
  - `build/transcripts/jc_dos_v0_7.txt`
  - `build/transcripts/jc_dos_v0_8.txt`
  - `build/transcripts/jc_dos_v0_9.txt`
  - `build/transcripts/jc_dos_v1_0.txt`

Script
- `scripts/release_gate_v1_0.sh` performs all checks.
- Requirements: `genspec`, `transcript_cmp`, and Python in PATH.
- The script fails on any mismatch and exits nonzero.

Spec hash updates
- Only regenerate the manifest after a version bump that permits spec changes.
- Command:
  `python scripts/spec_hash.py --repo-root . --manifest source/common/spec/spec_hashes_v1_0.txt --write`

Transcript integrity
- Capture transcripts as raw bytes with no line ending translation.
- Any normalization changes CRC32 and will fail the gate.
