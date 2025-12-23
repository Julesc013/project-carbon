# Am95xx Numeric Policy (v1)

This document summarizes the numeric behavior for the Am95xx accelerator family.

## Rounding

- All CAI paths use the per-context rounding mode:
  - `RN` (nearest-even), `RZ`, `RP`, `RM`.
- Rounding mode is shared by scalar, vector, and tensor tiers.

## Exceptions and flags

- IEEE flags are **sticky** per context: NV/DZ/OF/UF/NX.
- Flags are **ORed** into the context and into `ext_status` on completion.
- No exception traps or masks are implemented in v1.

## Determinism

- Scalar operations are deterministic and ordered.
- Vector operations aggregate flags across lanes; masked lanes pass through `op0`.
- Tensor operations execute in a fixed loop order with deterministic accumulation.

## Accumulation policy

- FP16/BF16 inputs accumulate in FP32.
- FP32 inputs accumulate in FP32.
- Result conversion follows the requested destination format.

## Conversion policy

- FP16/BF16 <-> FP32 conversions are supported.
- Int conversions: `i32<->f32`, `i64<->f64`.
- Float-to-int saturates on overflow and sets `NV` (and `NX` when inexact).

## Accuracy notes

- v1 prioritizes determinism and synthesizability over full IEEE 754 accuracy.
- Transcendentals use approximate implementations (binary64 uses binary32 kernels).
- Subnormal handling may flush to zero in fast paths.
