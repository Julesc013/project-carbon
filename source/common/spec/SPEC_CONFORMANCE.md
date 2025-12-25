# SPEC_CONFORMANCE (v1.0)

Purpose
- Define the canonical conformance transcript format for parity gating.

Versioning
- Version format: major.minor.
- Major mismatch: reject transcript.
- Minor greater than supported: reject transcript.
- Minor lower or equal: accept; reserved tokens remain reserved.

Binary layout
- Transcript is ASCII text.
- Each line ends with LF (0x0A) only; CR is not permitted.
- Tokens are separated by a single space; no leading or trailing spaces.
- Hex values are uppercase and zero-padded to 8 digits unless noted.

Header lines (exact order)
1) JC_CONFORMANCE 1
2) CONTRACTS SPEC_TIERS=1.0 SPEC_PROFILES=1.0 SPEC_MODE=1.0 SPEC_DISCOVERY=1.0
   SPEC_CAPSET=1.0 SPEC_TOPOLOGY=1.0 SPEC_BDT=1.0 SPEC_IRQ=1.0
   SPEC_DEV_UART=1.0 SPEC_DEV_TIMER=1.0 SPEC_DEV_PIC=1.0
   SPEC_DEV_STORAGE_IDEPIO=1.0 SPEC_CAI=1.0 SPEC_JCOM=1.0
   SPEC_FS_CPMX=1.0 SPEC_CONFORMANCE=1.0
3) CAPSET_CRC32 XXXXXXXX
4) BDT_CRC32 XXXXXXXX

Test lines
- TEST <ID> PASS
- TEST <ID> FAIL <ERROR>
- <ID> is 1..32 chars of A-Z, 0-9, or '_'.
- <ERROR> is a 4-digit hex jc_error_t value.

Result line
- RESULT PASS
- RESULT FAIL

CRC32 line
- CRC32 XXXXXXXX
- CRC32 covers all transcript bytes from the first character of the first line
  through the LF terminating the RESULT line. The CRC32 line is excluded.

Hash rules
- CAPSET_CRC32 is CRC32 over JC_CAPSET_V1 bytes (size_bytes length).
- BDT_CRC32 is CRC32 over the BDT region excluding the footer
  (matches JC_BDT_FOOTER_V1.crc32).
- Transcript CRC32 uses the CRC32 (IEEE) parameters below.

CRC32
- Polynomial: 0x04C11DB7 (IEEE).
- Init value: 0xFFFFFFFF.
- Input/output reflected.
- Final XOR: 0xFFFFFFFF.

Invariants
- Lines appear exactly in the order defined above; no extra lines are permitted.
- The CONTRACTS line is a single line; wrapping in this document is for display only.
- CAPSET_CRC32 and BDT_CRC32 are required even if their values are 0.
- For v1 reference targets, allowed-diff policy is none (byte-for-byte match).

Failure semantics
- Any formatting violation, CRC mismatch, or contract version mismatch is FAIL.
- If any TEST line is FAIL, RESULT must be FAIL.
