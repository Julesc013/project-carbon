EE CPM80 Conformance (v1.0)

Build:
- Compile ee_cpm80_conformance.c with jc_ee.c and ee_cpm80.c.

Expected transcript:
- EE_CONFORMANCE CPM80 1.0
- TEST RUN/FILE_IO/CONSOLE lines with PASS/FAIL.
- TEST NEG_UNSUPPORTED and TEST NEG_ILLEGAL lines.
- RESULT PASS or RESULT FAIL.
- TRANSCRIPT_CRC32 line.

Notes:
- NEG_UNSUPPORTED and NEG_ILLEGAL are special filenames for fault injection.
