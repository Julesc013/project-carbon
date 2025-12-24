# Verification

Project Carbon uses a layered verification flow focused on correctness and
determinism over performance. The source of truth for regression coverage is
`hdl/sim/tests/regress.yaml`.

## Test Layers

- Contract tests: validate fabric, CSR, IRQ, and CAI protocol behavior. These
  are fast, deterministic, and should run on every change (including discovery
  table contracts).
- Core tests: unit-level validation for individual CPU/FPU cores.
- System tests: smoke-level integration tests for full system top-levels.

Contract tests live under `hdl/sim/tb/` with shared BFMs under `hdl/sim/bfm/`.

## Running Tests

- Default (contract suite):
  - `scripts/run_sim.sh`
  - `scripts/run_sim.ps1`
- All contract tests:
  - `scripts/run_sim.sh --suite contract`
  - `scripts/run_sim.ps1 -Suite contract`
- All tests in the manifest (contract + core + system + optional):
  - `scripts/run_sim.sh --all`
  - `scripts/run_sim.ps1 -All`
- Override deterministic seed:
  - `scripts/run_sim.sh --seed 123`
  - `scripts/run_sim.ps1 -Seed 123`

## Deterministic Policy

Regression runs must be deterministic. Testbenches should use fixed seeds for
randomization and avoid unseeded `$urandom` usage. The simulation runner passes
`+SEED=<n>` (default `1`); override via `--seed` or `CARBON_SEED`. If a test
needs variability, use the `SEED` plusarg with a fixed fallback.
