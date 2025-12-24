# Accelerator Fabric (CAI)

This document describes the Carbon Accelerator Interface (CAI), the canonical queue model for accelerators and
high-throughput peripherals.

## Queue Model

- Submission and completion rings live in memory; software is producer, hardware is consumer (submit) and vice versa (complete).
- A doorbell CSR notifies the device that new descriptors are available.
- **Ordering**: fence before ringing the doorbell; fence after reading completion records before consuming results.

## Descriptor Header

Common header fields used by CAI submission descriptors:

- `version`
- `opcode_group`
- `opcode`
- `context`
- `tag`
- `flags`

## Opcode Groups

- `AM95_SCALAR` (P2)
- `AM95_VECTOR` (P3)
- `AM95_TENSOR` (P4)
- `DMA_COPY` (future)
- `DMA_FILL` (future)
- `UART_STREAM` (future)

## Completion Record

- `tag` (matches submission)
- `status` (completion code)
- optional IEEE flags in `ext_status`

## BDT Integration

- CAI-capable devices appear in the BDT with CAI queue count and doorbell offset.
- Rings are memory-resident; BDT + CSR metadata describes how software maps them.
