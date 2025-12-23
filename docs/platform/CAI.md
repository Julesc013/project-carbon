# Carbon Accelerator Interface (CAI) v1

This document summarizes the **Carbon Accelerator Interface (CAI)** contract
used by the Am95xx lineage and other accelerators. It is intentionally brief;
the authoritative field layouts live in the generated contract reference.

## Sources of truth

- `hdl/spec/cai.yaml` (source-of-truth)
- `docs/ARCH_CONTRACTS.md` (generated reference)
- RTL interfaces: `hdl/common/if/cai_if.sv`

## Contract summary

- **Queue model:** descriptor submit ring + completion ring
- **Descriptor version:** v1 (as defined in `ARCH_CONTRACTS.md`)
- **Ordering:** deterministic; completions occur in submission order unless
  explicitly defined otherwise by the descriptor flags
- **Addressing:** 64-bit descriptor pointers, SYS16 systems use low 16-bit decode
- **Feature exposure:** via discovery and CSR windows (see `ARCH_CONTRACTS.md`)

## Determinism rules

- No speculative I/O side effects through CAI.
- Fixed completion ordering per the descriptor contract.
- Deterministic rounding/exception behavior as documented in the FPU policy:
  `docs/fpu/Am95xx_NUMERIC_POLICY.md`.

## Deferred items

- Additional opcode groups beyond scalar/vector/tensor v1 sets.
- Multi-queue QoS arbitration and preemption.
- Interrupt-driven completion flows (polling is the v1 baseline).
