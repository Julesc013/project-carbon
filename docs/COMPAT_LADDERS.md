# Compatibility Ladders

This document summarizes the v1 tier ladders and presentation rules for CPU and FPU lineages.

## 8080-derived CPU ladder (Z80 lineage)

| Tier | Label | Notes |
|---:|---|---|
| P0 | 8080 | Reset default. |
| P1 | 8085 | 8080-compatible increment. |
| P2 | Z80 | Baseline Z80 compatibility tier. |
| P3 | Z180 | Z180 compatibility tier. |
| P4 | eZ80 | ADL / 24-bit mode tier. |
| P5 | Z280 | Protected/supervisor class tier. |
| P6 | Z380 | 32-bit extended Z80 architecture. |
| P7 | Z480 | Native 64-bit tier. |
| P8-P15 | Reserved | Reserved for future tiers. |

Presentation rules (reported via discovery):
- Z85 presents as P2 (Z80); undocumented Z80 behavior is reported via Z85_UNDOC_Z80.
- Z90 presents as P3 (Z180-compatible); Z90_Z180_CLASS marks the class.
- Z380 presents as P6; Z380_32BIT_EXTENDED marks 32-bit extensions.
- Z480 presents as P7; Z480_NATIVE_64 marks native 64-bit mode.

## Am95xx FPU ladder

| Tier | Label | Notes |
|---:|---|---|
| P0 | Am9511 | Base numeric engine. |
| P1 | Am9512-plus | IEEE FP32/FP64 and restored Am9511 functions. |
| P2 | Am9513 | Native async scalar IEEE engine; CAI-native. |
| P3 | Am9514 | Vector/SIMD math tier. |
| P4 | Am9515 | Matrix/tensor math tier. |
| P5-P15 | Reserved | Reserved for future tiers. |

Feature bits for optional capabilities:
- AM9512_IEEE_PLUS
- AM9513_ASYNC_SCALAR
- AM9514_VECTOR
- AM9515_TENSOR

## Presentation and discovery

Presented tiers for CPU and FPU lineages are reported via the discovery leaf model (CPUID/CAPS). Optional
superset behaviors are described via feature bits rather than elevating the presented tier. Reset always
starts in P0, and tier transitions occur only via MODEUP(target, entry) and RETMD().
