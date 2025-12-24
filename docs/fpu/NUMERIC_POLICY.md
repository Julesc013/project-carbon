# Am95xx Numeric Policy (v1)

This document summarizes the numeric behavior for the Am95xx accelerator family.
`docs/fpu/Am95xx_NUMERIC_POLICY.md` mirrors this content for compatibility.

## Rounding modes

- All CAI paths use the per-context rounding mode:
  - `RN` (nearest-even), `RZ` (toward zero), `RP` (toward +inf), `RM` (toward -inf).
- Rounding mode is shared by scalar, vector, and tensor tiers.
- Legacy P0/P1 stack operations use the same rounding mode.

## Exceptions and flags

- IEEE flags are **sticky** per context: NV/DZ/OF/UF/NX.
- Flags are **ORed** into the context and into `ext_status` on completion.
- No exception traps or masks are implemented in v1.

## NaN and subnormal policy

- Signaling NaNs are treated as invalid and converted to quiet NaNs.
- Quiet NaNs propagate; invalid operations return a canonical quiet NaN.
- Subnormals may flush to zero in fast paths; flush sets UF/NX as appropriate.

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
- Decimal floating-point and full IEEE edge-case compliance are deferred.
