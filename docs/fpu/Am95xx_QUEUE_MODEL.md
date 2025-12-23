# Am95xx CAI Queue Model (v1)

This document describes how the Am95xx accelerator family consumes CAI
descriptors and produces completion records.

## Overview

- The accelerator uses the **CAI submit ring** for P2/P3/P4 work.
- A host writes a submit descriptor into the ring and pulses
  `cai.submit_doorbell`.
- The device processes descriptors **in order**, with a single-outstanding
  fabric access model for determinism.

## Submit ring

- `submit_desc_base` and `submit_ring_mask` are host-provided.
- The descriptor `desc_version` and `desc_size_dw` must match v1 values.
- `opcode_group` selects scalar (`P2`), vector (`P3`), or tensor (`P4`) tiers.
- `context_id` selects the execution context; `0xFFFF` means use `cai.context_sel`.

## Completion ring

- `comp_base` / `comp_ring_mask` are configured via CSRs.
- Each completion record reports:
  - `tag` (copied from submit descriptor)
  - `status` (`CARBON_CAI_STATUS_*`)
  - `ext_status` (low bits carry IEEE flags NV/DZ/OF/UF/NX)
  - `bytes_written`
- `comp_doorbell` pulses on completion; `comp_irq` asserts if enabled.

## Ordering and fences

- Software must ensure the descriptor and operand buffers are globally visible
  before ringing the doorbell (use ordered fabric attributes or explicit fences).
- Results and completion records are written after the operation completes.

## Mode selection

- Default mode comes from `CARBON_CSR_AM9513_MODE`.
- Per-descriptor override uses `submit_desc.flags[MODE_VALID]` and the mode field.

## Determinism guarantees

- Descriptors execute in submission order.
- There is no speculative I/O or out-of-order completion in v1.
