# Am95xx Family Overview (P0–P4)

This document summarizes the Am95xx lineage as implemented in Project Carbon.
All tiers are hosted by the shared Am95xx accelerator block (`am9513_accel`)
and are discoverable via the standard discovery/BDT model.

## Tiers and personalities

| Tier | Personality | Summary |
|---:|---|---|
| P0 | Am9511 | Legacy stack-based scalar engine. |
| P1 | Am9512-plus | IEEE FP32/FP64 + restored Am9511 functions. |
| P2 | Am9513 | Async scalar IEEE engine (CAI-native). |
| P3 | Am9514 | Vector/SIMD tier (CAI-native). |
| P4 | Am9515 | Matrix/tensor tier (CAI-native). |

Implementation coverage is a v1 subset; see the per-tier docs for the exact
operations currently implemented.

## Interfaces and pairing model

- **P2–P4 are CAI-native**: all work is submitted via CAI descriptor rings.
- **P0/P1 legacy** personalities are exposed via the legacy CSR/MMIO window.
- Any Carbon CPU can pair with any Am95xx tier; CPUs remain FP-free and use
  discovery + CAI (or legacy MMIO for P0/P1) to access floating-point.

## Discovery and feature bits

- `presented_fpu_tier` reports the highest active Am95xx tier.
- Feature bits advertise optional capabilities:
  - `AM9512_IEEE_PLUS`, `AM9513_ASYNC_SCALAR`, `AM9514_VECTOR`, `AM9515_TENSOR`.

## x87 capability parity (capabilities, not ABI)

- **P0** targets 8087-class scalar capability (deterministic math, rich ops).
- **P1** targets 287/387-class IEEE FP32/FP64 capability and environment flags.
- **P2** targets 486/Pentium-era scalar capability with async queueing/FMA.
- **P3/P4** extend beyond x87 into SIMD and tensor capabilities.

## Determinism

- Operations are deterministic for a given tier, mode, and input set.
- See `docs/fpu/NUMERIC_POLICY.md` and `docs/fpu/Am95xx_QUEUE_MODEL.md`.

## Related docs

- `docs/fpu/Am9513.md`, `docs/fpu/Am9514.md`, `docs/fpu/Am9515.md`
- `docs/fpu/NUMERIC_POLICY.md`
- `docs/platform/CPU_FPU_BOUNDARY.md`
