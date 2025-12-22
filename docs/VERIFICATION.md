# Verification

Project Carbon uses a layered verification flow focused on correctness and
determinism over performance. The source of truth for regression coverage is
`hdl/sim/tests/regress.yaml`.

## Test Layers

- Contract tests: validate fabric, CSR, IRQ, and CAI protocol behavior. These
  are fast, deterministic, and should run on every change.
- Core tests: unit-level validation for individual CPU/FPU cores.
- System tests: smoke-level integration tests for full system top-levels.

Contract tests live under `hdl/sim/tb/` with shared BFMs under `hdl/sim/bfm/`.

## Running Tests

- All contract tests:
  - `scripts/run_sim.sh --all --suite contract`
  - `scripts/run_sim.ps1 -All -Suite contract`
- All tests in the manifest:
  - `scripts/run_sim.sh --all`
  - `scripts/run_sim.ps1 -All`

## Deterministic Policy

Regression runs must be deterministic. Testbenches should use fixed seeds for
randomization and avoid unseeded `$urandom` usage. If a test needs variability,
use an explicit plusarg with a fixed default to keep CI stable.
