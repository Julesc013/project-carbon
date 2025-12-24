# CPU/FPU Boundary (v1)

This document defines the hard separation between Carbon CPUs and the Am95xx
floating-point lineage.

## Contract summary

- Carbon CPUs (Z85/Z90/Z380/Z480) implement **integer-only** ISAs with **no FP
  registers or instructions**.
- All floating-point execution is provided by Am95xx accelerator tiers.
- CPU tier transitions use `MODEUP/RETMD`; FPU tiers are **independent** and are
  discovered, not switched by CPU opcodes.

## Pairing model

- Any CPU tier may pair with any Am95xx tier.
- Pairing is discovered via the canonical discovery record:
  - `presented_fpu_tier`
  - FPU feature bits (`AM9512_IEEE_PLUS`, `AM9513_ASYNC_SCALAR`, `AM9514_VECTOR`,
    `AM9515_TENSOR`)
- The accelerator appears in the BDT with its CAI doorbell and ring pointers.

## Native vs legacy interfaces

- **P2–P4** are **CAI-native** and must be accessed via CAI queues.
- **P0/P1** may expose a legacy stack interface via the CSR/MMIO window.
- Systems may provide both interfaces, but CAI is mandatory for P2–P4.

## Determinism and safety

- CAI submission/completion ordering defines architectural determinism.
- Numeric determinism rules are defined in `docs/fpu/NUMERIC_POLICY.md`.
