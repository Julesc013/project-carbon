# CarbonDMA v1.0 (Project Carbon)

This document describes the CarbonDMA multi-channel DMA engine in `hdl/cores/CarbonDMA/`.

## 1. Dual personality model

CarbonDMA exposes two personalities:

- **Compatibility personality**: register-programmed DMA via a fabric-attached compat window.
- **Turbo personality**: standard turbo queue submission/completion rings (descriptor mode).

Both personalities provide deterministic polling completion; interrupts are optional and not implemented in v1.

## 2. Compatibility register map

Compatibility register offsets are defined in `carbondma_pkg.sv`:

- `CARBONDMA_COMPAT_ID_OFF`, `CARBONDMA_COMPAT_STATUS_OFF`, `CARBONDMA_COMPAT_CTRL_OFF`
- `CARBONDMA_COMPAT_CH_SEL_OFF` selects the active channel
- `CARBONDMA_COMPAT_CH_SRC_LO/HI`, `CARBONDMA_COMPAT_CH_DST_LO/HI`
- `CARBONDMA_COMPAT_CH_LEN`, `CARBONDMA_COMPAT_CH_CTRL`, `CARBONDMA_COMPAT_CH_STATUS`
- `CARBONDMA_COMPAT_CH_ATTR`, `CARBONDMA_COMPAT_CH_FILL`

Channel control bits:

- `CH_CTRL[0]`: start
- `CH_CTRL[1]`: fill (1=fill, 0=copy)

Channel status bits (polling completion):

- `CH_STATUS[0]`: busy
- `CH_STATUS[1]`: done (write to clear)
- `CH_STATUS[2]`: error (write to clear)

## 3. Turbo queue interface

CarbonDMA implements the standard turbo queue model:

- Submission ring configured by `CARBONDMA_QUEUE_SUBMIT_*` CSRs.
- Completion ring configured by `CARBONDMA_QUEUE_COMP_*` CSRs.
- Doorbell (`CARBONDMA_QUEUE_DOORBELL`) provides the producer tail.

Submission descriptors use `TURBO_SUBMIT_DESC_V1` (32 bytes). The `data_ptr`
points to one or more `CARBONDMA_DESC_V1` entries:

```
CARBONDMA_DESC_V1 (32 bytes):
  src (u64)
  dst (u64)
  len (u32)
  flags (u32)   // bit0 = fill
  fill (u32)
  attr (u32)    // [15:0]=src attr, [31:16]=dst attr
```

`data_len` and `data_stride` control the number of entries and their spacing.

Completion records follow `TURBO_COMP_REC_V1` (tag, status, bytes_written).

## 4. Determinism and limitations (v1)

- Byte-granular transfers (one byte per fabric transaction).
- 32-bit fabric addresses only; upper 32 bits are ignored.
- One outstanding DMA engine shared by all channels and queue entries.
- No CRC32 assist in v1.
- No interrupt delivery in v1 (poll status or completion ring).
