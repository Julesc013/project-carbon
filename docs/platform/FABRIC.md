# Carbon Fabric (SYS16) v1

This document summarizes the v1 memory fabric contract used by Carbon systems.
It is a compact pointer to the authoritative specs and generated contracts.

## Sources of truth

- `hdl/spec/fabric.yaml` (source-of-truth)
- `docs/ARCH_CONTRACTS.md` (generated reference)
- RTL interfaces: `hdl/common/if/fabric_if.sv`

## Contract summary

- **Handshake:** ready/valid request + response channels
- **Attributes:** ordered/uncacheable bits are defined in `ARCH_CONTRACTS.md`
- **Responses:** error codes and latency expectations are specified in the
  generated contracts; do not invent new response values in RTL
- **Ordering:** ordered requests are strictly preserved; unordered traffic may
  reorder subject to fabric rules

## Determinism rules

- I/O transactions must use ordered/uncacheable attributes.
- Arbitration must be deterministic in the absence of randomized inputs.
- All fabric adapters must preserve response IDs per the contract.

## Deferred items

- Multi-clock fabric bridges and clock-domain crossing behavior.
- Coherency protocols beyond the v1 ordered/uncacheable model.
