# HDL Simulation (v1.0)

Project Carbon uses a small set of SystemVerilog smoke tests and contract tests under `hdl/sim/`.

## Prerequisites

- Python (for `scripts/gen_arch.*`)
- `make`
- Icarus Verilog: `iverilog` + `vvp`

## Quick start

- Generate architecture constants: `scripts/gen_arch.sh` (Linux/macOS) or `scripts/gen_arch.ps1` (Windows)
- Run all regression tests: `scripts/run_sim.sh --all` or `scripts/run_sim.ps1 -All`
- Run a single test by Make target: `make -C hdl/sim tb_carbonz80`

## Regression manifest

`hdl/sim/tests/regress.yaml` defines the default ordered set of tests executed by `scripts/run_sim.*`.

## Notes

- The simulation Makefile currently targets Icarus Verilog (`iverilog`).
- If a simulator is missing, `scripts/run_sim.*` fails with a clear dependency message.

