# Device Model: Compatibility vs Turbo (v1)

Project Carbon devices implement a dual-personality model so legacy RC2014/CP/M code can run unchanged while modern firmware can unlock high-throughput paths.

## Dual Personality Model

Compatibility personality:
- Ordered I/O semantics; reads and writes observe program order.
- WAIT/backpressure is honored; no hidden reordering.
- Registers are deterministic; no turbo-only side effects.

Turbo personality:
- Uses fast data-plane paths (queues, DMA, large FIFOs).
- May complete faster or slower than compatibility mode, but results must match.
- Turbo features are gated by tier policy and MODEFLAGS.STRICT.

## Personality Selection and Gating

- MODEFLAGS.STRICT forces compatibility behavior even when turbo tiers are active.
- Devices expose DEVCSR_CTRL/MODE and per-device configuration to select turbo modes.
- Software must not assume turbo is active until it is explicitly enabled and confirmed.

## Polling-Complete Semantics

All devices must provide a deterministic completion indicator that can be polled:
- Compatibility operations must be observable via status bits or counters.
- Turbo queue operations must provide completion records and/or queue status.
- Interrupts are optional accelerators; polling must always work.

## Determinism Rules

- Different speeds are acceptable; different results are not.
- Compatibility mode must never see hidden turbo effects.
- Turbo mode may change timing but not functional outcomes.

## Standard Interfaces

Internal integration uses the canonical contracts:
- `fabric_if` for data-plane transactions.
- `csr_if` for control/status.
- `cai_if` for accelerators where applicable.
- Debug/trace interface for introspection.

For details, see `docs/ARCH_CONTRACTS.md` and the spec YAMLs under `hdl/spec/`.
