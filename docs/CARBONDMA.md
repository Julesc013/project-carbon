# CarbonDMA (v1)

CarbonDMA is the standard multi-channel DMA engine for Project Carbon systems. It supports
compatibility (register-programmed) DMA and optional turbo queue submissions.

## Discovery / BDT

In BDT, CarbonDMA is reported as a DMA-class device with feature words indicating:
- DMA channel count (default: 4)
- Queue count (0 in v1 sim; 1 in RTL)

Compatibility access is exposed through the BSP-defined CarbonDMA base window.

## Compatibility Programming Model

1. Select a channel via `CH_SEL`.
2. Program `CH_SRC`, `CH_DST`, `CH_LEN`, and `CH_ATTR`.
3. Optionally set `CH_FILL` and `CH_CTRL.FILL`.
4. Write `CH_CTRL.START` to launch the transfer.
5. Poll `CH_STATUS.DONE` (or global `STATUS.BUSY`) for completion.

## Turbo Queue Model

Turbo queue submission uses the standard `TURBO_SUBMIT_DESC_V1` format with a
device-specific payload (scatter/gather entries). Completion records follow
`TURBO_COMP_REC_V1`.

## Determinism

DMA completion is always observable via polling. Turbo mode may change timing,
but results must match compatibility mode.

## Register Map

See `hdl/cores/CarbonDMA/docs/CarbonDMA_v1.md` for the full register map and bit definitions.
