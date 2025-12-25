# Bringup FPGA_REF

Purpose
- Capture deterministic conformance transcripts from FPGA_REF over serial.

Prerequisites
- FPGA_REF bitstream and BSP build with CarbonKIO UART enabled.
- Serial capture tool that records raw bytes without translation.

Capture steps
1. Program the FPGA with the FPGA_REF image.
2. Connect the UART using BSP-defined baud, parity, and flow settings.
3. Disable local echo and newline conversion in the capture tool.
4. Boot BIOS/DOS and run the requested conformance build.
5. Save the raw output to a transcript file.

Transcript comparison
- Use `transcript_cmp` to compare against the matching golden transcript.
- Place captured output under `build/transcripts/` using the standard filenames.

Notes
- Do not edit or normalize line endings; the CRC32 depends on exact bytes.
