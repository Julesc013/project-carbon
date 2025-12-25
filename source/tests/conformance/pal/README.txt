PAL Conformance (v1.0)

Build:
- Compile pal_conformance.c with a PAL bound via jc_pal_*_bind().

Expected transcript:
- Header lines (PAL_CONFORMANCE, PAL_ABI, BDT_CRC32, CAPSET_CRC32).
- TEST BOOT/BLOCK_IO/FS/RUN lines with PASS/FAIL.
- TEST NEG_* lines for fault injection hooks.
- RESULT PASS or RESULT FAIL.
- TRANSCRIPT_CRC32 line.

Notes:
- FS test passes only if LBA0 contains a valid CPMX superblock.
- Unsupported or missing PAL prints RESULT SKIP with CRC.
