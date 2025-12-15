# ZEX Harness (skeleton)

ZEXDOC/ZEXALL are common Z80 instruction test suites.

This repository does not bundle ZEX binaries. To run them in simulation:

1. Convert the ZEX binary to a simulator-friendly memory init format (hex bytes).
2. Load it into the `fabric_mem_bfm` memory array at the desired base address.
3. Run the core until it reports completion (commonly via an I/O signature port).

## Intended contract

- ZEX is typically executed from a fixed address with CP/M-style BDOS stubs.
- Completion is often detected by:
  - writes to a specific I/O port, or
  - writes into a known RAM mailbox location.

## Status

This is a **placeholder** harness skeleton. The current `z85_core` RTL does not yet implement the full Z80 ISA required to pass ZEX.

