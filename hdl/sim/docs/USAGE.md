# Simulation Usage

## Prerequisites

- Python (python3 or python)
- make
- Simulator: Verilator or Icarus Verilog (iverilog + vvp)

## Quick Start

- Generate architecture constants:
  - `scripts/gen_arch.sh` (Linux/macOS)
  - `scripts/gen_arch.ps1` (Windows)
- Run the default contract suite:
  - `scripts/run_sim.sh`
  - `scripts/run_sim.ps1`
- Run all contract tests:
  - `scripts/run_sim.sh --suite contract`
  - `scripts/run_sim.ps1 -Suite contract`
- Run all tests in the manifest:
  - `scripts/run_sim.sh --all`
  - `scripts/run_sim.ps1 -All`
- Override deterministic seed:
  - `scripts/run_sim.sh --seed 123`
  - `scripts/run_sim.ps1 -Seed 123`
- Run a single test target:
  - `scripts/run_sim.sh --test tb_fabric_contract`
  - `scripts/run_sim.ps1 -Test tb_fabric_contract`
- List available tests:
  - `scripts/run_sim.sh --list --suite contract`
  - `scripts/run_sim.ps1 -List -Suite contract`
- List optional local tests:
  - `scripts/run_sim.sh --list --suite optional`
  - `scripts/run_sim.ps1 -List -Suite optional`

Logs are written to `hdl/sim/build/logs`.

## Regression Manifest

`hdl/sim/tests/regress.yaml` is the source of truth for regression suites. It
defines named sections:

- `contract_tests` for interface and fabric contracts
- `core_tests` for core-level unit tests
- `system_smoke_tests` for minimal system smoke/tier tests
- `system_tests` for full system tests
- `placeholder_tests` for not-yet-implemented targets (not run by default)
- `optional_local_tests` for local-only tests that may require extra assets

To add a new TB:

1. Add the TB source under `hdl/sim/tb/`.
2. Add a Makefile target under `hdl/sim/Makefile`.
3. Add the target name to the appropriate section in `regress.yaml`.

## Deterministic Seeding

Contract tests must be deterministic. Use fixed seeds in testbenches (for
example, a localparam or LFSR seed), and avoid unseeded `$urandom` calls. The
runner passes `+SEED=<n>` (default `1`); override via `--seed` or `CARBON_SEED`.
If a test needs configurable variability, use the `SEED` plusarg and provide a
fixed fallback.

## Simulator Selection

`scripts/run_sim.*` will use Verilator if it is available, otherwise it falls
back to Icarus Verilog. You can always invoke a specific test directly with:

```
make -C hdl/sim tb_fabric_contract
```
